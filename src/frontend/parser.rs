// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::env::{
    ConstructorData, Declar, DeclarInfo, InductiveData, RecursorData, ReducibilityHint,
};
use crate::config::{AxiomDecision, Config};
use crate::hash64;
use crate::outcome::{decline, ensure, reject, unsupported};
use crate::term::expr::Expr;
use crate::term::hash::{FxHashMap, FxIndexMap, new_fx_hash_map, new_fx_index_map};
use crate::term::intern::Dag;
use crate::term::level::Level;
use crate::term::name::Name;
use crate::term::ptr::{BigUintPtr, ExprPtr, LevelPtr, LevelsPtr, NamePtr, StringPtr};
use bumpalo::Bump;
use num_bigint::BigUint;
use serde::de::{Error as DeError, Visitor};
use serde::{Deserialize, Deserializer};
use std::borrow::Cow;
use std::error::Error;
use std::fmt;
use std::io::Read;
use std::sync::Arc;
use std::sync::mpsc::{Receiver, SyncSender, channel, sync_channel};

fn check_semver(meta: &FileMeta<'_>) -> Result<(), Box<dyn Error>> {
    const MIN_SEMVER: semver::Version = semver::Version::new(3, 1, 0);
    const MAX_SEMVER: semver::Version = semver::Version::new(3, 2, 0);
    let export_file_semver = semver::Version::parse(&meta.format.version)?;
    if export_file_semver < MIN_SEMVER {
        decline(format!(
            "export format version is less than the minimum supported version. Found {export_file_semver}, but min supported is {MIN_SEMVER}"
        ))
    } else if export_file_semver >= MAX_SEMVER {
        decline(format!(
            "export format version is greater than the maximum supported version. Found {export_file_semver}, but max (exclusive) supported is {MAX_SEMVER}"
        ))
    } else {
        Ok(())
    }
}

pub struct Parser<'a> {
    arena: &'a Bump,
    dag: Dag<'a>,
    anon: NamePtr<'a>,
    zero: LevelPtr<'a>,
    names_by_idx: Vec<Option<NamePtr<'a>>>,
    levels_by_idx: Vec<Option<LevelPtr<'a>>>,
    exprs_by_idx: Vec<ExprEntry<'a>>,
    declars: FxIndexMap<NamePtr<'a>, Declar<'a>>,
    config: Config,
    mutual_block_sizes: FxHashMap<NamePtr<'a>, (usize, usize)>,
    scratch_idxs: Vec<u32>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct LeanMeta<'a> {
    version: Cow<'a, str>,
    githash: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct ExporterMeta<'a> {
    name: Cow<'a, str>,
    version: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct FormatMeta<'a> {
    version: Cow<'a, str>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct FileMeta<'a> {
    lean: LeanMeta<'a>,
    exporter: ExporterMeta<'a>,
    format: FormatMeta<'a>,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum BackRef {
    #[serde(alias = "in")]
    In(u32),
    #[serde(alias = "il")]
    Il(u32),
    #[serde(alias = "ie")]
    Ie(u32),
}

impl BackRef {
    fn index(self) -> u32 {
        match self {
            BackRef::In(i) | BackRef::Il(i) | BackRef::Ie(i) => i,
        }
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
struct ExportJsonObject<'a> {
    #[serde(flatten)]
    val: ExportJsonVal<'a>,
    #[serde(flatten)]
    i: Option<BackRef>,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
enum DefinitionSafety {
    #[serde(rename = "unsafe")]
    Unsafe,
    #[serde(rename = "safe")]
    Safe,
    #[serde(rename = "partial")]
    Partial,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum QuotKind {
    #[serde(rename = "type")]
    Ty,
    #[serde(rename = "ctor")]
    Ctor,
    #[serde(rename = "lift")]
    Lift,
    #[serde(rename = "ind")]
    Ind,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct RecursorRule {
    ctor: u32,
    nfields: u16,
    rhs: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct IndInfo {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    all: Vec<u32>,
    ctors: Vec<u32>,
    #[serde(rename = "isRec")]
    is_rec: bool,
    #[serde(rename = "isReflexive")]
    is_reflexive: bool,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numNested")]
    num_nested: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Constructor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    cidx: u16,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numFields")]
    num_fields: u16,
    induct: u32,
}

#[derive(Debug, Clone, PartialEq, Eq, Hash, Deserialize)]
struct Recursor {
    name: u32,
    #[serde(rename = "levelParams")]
    uparams: Vec<u32>,
    #[serde(rename = "type")]
    ty: u32,
    #[serde(rename = "isUnsafe")]
    is_unsafe: bool,
    #[serde(rename = "numParams")]
    num_params: u16,
    #[serde(rename = "numIndices")]
    num_indices: u16,
    #[serde(rename = "numMotives")]
    num_motives: u16,
    #[serde(rename = "numMinors")]
    num_minors: u16,
    rules: Vec<RecursorRule>,
    all: Vec<u32>,
    k: bool,
}

#[derive(Debug, Clone, PartialEq, Eq, Deserialize)]
enum ExportJsonVal<'a> {
    // The exporter metadata, incl. info about the lean, exporter, and format versions used
    // to create the export file.
    #[serde(rename = "meta")]
    Metadata(FileMeta<'a>),
    #[serde(rename = "str")]
    NameStr { pre: u32, str: Cow<'a, str> },
    #[serde(rename = "num")]
    NameNum { pre: u32, i: u32 },
    #[serde(rename = "succ")]
    LevelSucc(u32),
    #[serde(rename = "max")]
    LevelMax([u32; 2]),
    #[serde(rename = "imax")]
    LevelIMax([u32; 2]),
    #[serde(rename = "param")]
    LevelParam(u32),
    #[serde(
        rename = "natVal",
        deserialize_with = "deserialize_biguint_from_string"
    )]
    NatLit(BigUint),
    #[serde(rename = "strVal")]
    StrLit(Cow<'a, str>),
    #[serde(rename = "mdata")]
    ExprMData { expr: u32, data: serde_json::Value },
    // Binder names and plicity are omitted so serde skips them as unknown fields.
    #[serde(rename = "letE")]
    ExprLet {
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        body: u32,
        nondep: bool,
    },
    #[serde(rename = "const")]
    ExprConst {
        name: u32,
        #[serde(rename = "us")]
        levels: Vec<u32>,
    },
    #[serde(rename = "app")]
    ExprApp {
        #[serde(rename = "fn")]
        fun: u32,
        arg: u32,
    },
    #[serde(rename = "forallE")]
    ExprPi {
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
    },
    #[serde(rename = "lam")]
    ExprLambda {
        #[serde(rename = "type")]
        binder_type: u32,
        body: u32,
    },
    #[serde(rename = "proj")]
    ExprProj {
        #[serde(rename = "typeName")]
        type_name: u32,
        idx: usize,
        #[serde(rename = "struct")]
        structure: u32,
    },
    #[serde(rename = "sort")]
    ExprSort(u32),
    #[serde(rename = "bvar")]
    ExprBVar(u16),
    #[serde(rename = "axiom")]
    Axiom {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
    },
    #[serde(rename = "thm")]
    Thm {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
    },
    #[serde(rename = "def")]
    Defn {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "hints")]
        hint: ReducibilityHint,
        //all: Vec<usize>,
        safety: DefinitionSafety,
    },
    #[serde(rename = "opaque")]
    Opaque {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        value: u32,
        #[serde(rename = "isUnsafe")]
        is_unsafe: bool,
    },
    #[serde(rename = "quot")]
    Quot {
        name: u32,
        #[serde(rename = "levelParams")]
        uparams: Vec<u32>,
        #[serde(rename = "type")]
        ty: u32,
        #[serde(rename = "kind")]
        kind: QuotKind,
    },
    #[serde(rename = "inductive")]
    Inductive {
        #[serde(rename = "types")]
        ind_vals: Vec<IndInfo>,
        #[serde(rename = "ctors")]
        ctor_vals: Vec<Constructor>,
        #[serde(rename = "recs")]
        rec_vals: Vec<Recursor>,
    },
}

pub(crate) fn parse_export_mapped<'p>(
    arena: &'p Bump,
    input: &[u8],
    config: Config,
) -> Result<crate::checker::context::ExportFile<'p>, Box<dyn Error>> {
    let mut parser = Parser::with_input_len(arena, config, input.len());
    parser.run_over(input)?;
    Ok(parser.finish())
}

const READ_CHUNK: usize = 1 << 22;
const READ_AHEAD: usize = 2;

struct Block {
    bytes: Vec<u8>,
    len: usize,
}

impl Block {
    fn new() -> Self {
        Block {
            bytes: vec![0; 2 * READ_CHUNK],
            len: 0,
        }
    }
}

fn read_blocks<R: Read>(
    mut reader: R,
    blocks: &SyncSender<std::io::Result<Block>>,
    spent: &Receiver<Block>,
) {
    let mut pending = Block::new();
    loop {
        if pending.bytes.len() - pending.len < READ_CHUNK {
            pending.bytes.resize(pending.len + READ_CHUNK, 0);
        }
        let read = match reader.read(&mut pending.bytes[pending.len..pending.len + READ_CHUNK]) {
            Ok(read) => read,
            Err(e) => {
                let _ = blocks.send(Err(e));
                return;
            }
        };
        pending.len += read;
        if read == 0 {
            break;
        }
        let filled = &pending.bytes[..pending.len];
        if let Some(last) = filled.iter().rposition(|b| *b == b'\n') {
            let tail = &filled[last + 1..];
            let mut next = spent.try_recv().unwrap_or_else(|_| Block::new());
            if next.bytes.len() < tail.len() {
                next.bytes.resize(tail.len(), 0);
            }
            next.bytes[..tail.len()].copy_from_slice(tail);
            next.len = tail.len();
            pending.len = last + 1;
            if blocks
                .send(Ok(std::mem::replace(&mut pending, next)))
                .is_err()
            {
                return;
            }
        }
    }
    if pending.len != 0 {
        let _ = blocks.send(Ok(pending));
    }
}

pub(crate) fn parse_export_file<R: Read + Send + 'static>(
    arena: &Bump,
    reader: R,
    config: Config,
) -> Result<crate::checker::context::ExportFile<'_>, Box<dyn Error>> {
    let mut parser = Parser::new(arena, config);
    let (blocks_tx, blocks_rx) = sync_channel(READ_AHEAD);
    let (spent_tx, spent_rx) = channel();
    std::thread::Builder::new()
        .name("reader".to_owned())
        .spawn(move || read_blocks(reader, &blocks_tx, &spent_rx))?;
    for block in blocks_rx {
        let block = block?;
        parser.run_over(&block.bytes[..block.len])?;
        let _ = spent_tx.send(block);
    }
    Ok(parser.finish())
}

struct Fallback;

const DIGIT_BIAS: u64 = 0x3030_3030_3030_3030;

#[inline(always)]
fn digit_run(unbiased: u64) -> u32 {
    let non_digit =
        (unbiased.wrapping_add(0x7676_7676_7676_7676) | unbiased) & 0x8080_8080_8080_8080;
    if non_digit == 0 {
        8
    } else {
        non_digit.trailing_zeros() / 8
    }
}

#[inline(always)]
fn packed_digits(unbiased: u64, run: u32) -> u64 {
    const MASK: u64 = 0x0000_00FF_0000_00FF;
    const MUL1: u64 = 0x000F_4240_0000_0064;
    const MUL2: u64 = 0x0000_2710_0000_0001;
    let v = unbiased << ((8 - run) * 8);
    let x = v.wrapping_mul(10).wrapping_add(v >> 8);
    (((x & MASK).wrapping_mul(MUL1)).wrapping_add(((x >> 16) & MASK).wrapping_mul(MUL2))) >> 32
}

#[inline]
fn find_newline(s: &[u8]) -> Option<usize> {
    const LO: u64 = 0x0101_0101_0101_0101;
    const HI: u64 = 0x8080_8080_8080_8080;
    const NL: u64 = 0x0a0a_0a0a_0a0a_0a0a;
    let mut i = 0;
    while i + 8 <= s.len() {
        let w = u64::from_le_bytes(s[i..i + 8].try_into().unwrap());
        let x = w ^ NL;
        let found = x.wrapping_sub(LO) & !x & HI;
        if found != 0 {
            return Some(i + (found.trailing_zeros() >> 3) as usize);
        }
        i += 8;
    }
    while i < s.len() {
        if s[i] == b'\n' {
            return Some(i);
        }
        i += 1;
    }
    None
}

const POW10: [u64; 8] = [1, 10, 100, 1_000, 10_000, 100_000, 1_000_000, 10_000_000];

struct Cur<'s> {
    s: &'s [u8],
    fast_end: usize,
    i: usize,
    next: usize,
}

impl<'s> Cur<'s> {
    #[inline(always)]
    fn lit(&mut self, l: &[u8]) -> Result<(), Fallback> {
        if self.s.len() - self.i < l.len() || &self.s[self.i..self.i + l.len()] != l {
            return Err(Fallback);
        }
        self.i += l.len();
        Ok(())
    }

    #[inline(always)]
    fn peek(&self, ahead: usize) -> Result<u8, Fallback> {
        self.s.get(self.i + ahead).copied().ok_or(Fallback)
    }

    #[inline(always)]
    fn uint(&mut self) -> Result<u64, Fallback> {
        if self.i < self.fast_end {
            let x = u64::from_le_bytes(self.s[self.i..self.i + 8].try_into().unwrap()) ^ DIGIT_BIAS;
            let run = digit_run(x);
            if run == 0 {
                return Err(Fallback);
            }
            if run < 8 {
                self.i += run as usize;
                return Ok(packed_digits(x, run));
            }
            let hi = packed_digits(x, 8);
            if self.s[self.i + 8].wrapping_sub(b'0') > 9 {
                self.i += 8;
                return Ok(hi);
            }
            let x = u64::from_le_bytes(self.s[self.i + 8..self.i + 16].try_into().unwrap())
                ^ DIGIT_BIAS;
            let run = digit_run(x);
            if run < 8 {
                self.i += 8 + run as usize;
                return Ok(hi * POW10[run as usize] + packed_digits(x, run));
            }
        }
        let (x, i) = uint_slow(self.s, self.i)?;
        self.i = i;
        Ok(x)
    }

    #[inline(always)]
    fn uint_u16(&mut self) -> Result<u16, Fallback> {
        self.uint()?.try_into().map_err(|_| Fallback)
    }

    #[inline(always)]
    fn uint_u32(&mut self) -> Result<u32, Fallback> {
        self.uint()?.try_into().map_err(|_| Fallback)
    }

    #[inline(always)]
    fn uint_usize(&mut self) -> Result<usize, Fallback> {
        self.uint()?.try_into().map_err(|_| Fallback)
    }

    #[inline(always)]
    fn quoted(&mut self) -> Result<&'s [u8], Fallback> {
        self.lit(b"\"")?;
        let start = self.i;
        while self.i < self.s.len() {
            match self.s[self.i] {
                b'"' => {
                    let r = &self.s[start..self.i];
                    self.i += 1;
                    return Ok(r);
                }
                b'\\' | b'\n' => return Err(Fallback),
                _ => self.i += 1,
            }
        }
        Err(Fallback)
    }

    #[inline(always)]
    fn quoted_str(&mut self) -> Result<&'s str, Fallback> {
        std::str::from_utf8(self.quoted()?).map_err(|_| Fallback)
    }

    #[inline(always)]
    fn boolean(&mut self) -> Result<bool, Fallback> {
        if self.peek(0)? == b't' {
            self.lit(b"true")?;
            Ok(true)
        } else {
            self.lit(b"false")?;
            Ok(false)
        }
    }

    #[inline]
    fn u32_array(&mut self, out: &mut Vec<u32>) -> Result<(), Fallback> {
        out.clear();
        self.lit(b"[")?;
        if self.peek(0)? == b']' {
            self.i += 1;
            return Ok(());
        }
        loop {
            out.push(self.uint_u32()?);
            match self.peek(0)? {
                b',' => self.i += 1,
                b']' => {
                    self.i += 1;
                    return Ok(());
                }
                _ => return Err(Fallback),
            }
        }
    }

    #[inline]
    fn skip_u32_array(&mut self) -> Result<(), Fallback> {
        self.lit(b"[")?;
        if self.peek(0)? == b']' {
            self.i += 1;
            return Ok(());
        }
        loop {
            self.uint()?;
            match self.peek(0)? {
                b',' => self.i += 1,
                b']' => {
                    self.i += 1;
                    return Ok(());
                }
                _ => return Err(Fallback),
            }
        }
    }

    #[inline]
    fn hint(&mut self) -> Result<ReducibilityHint, Fallback> {
        if self.peek(0)? == b'{' {
            self.lit(b"{\"regular\":")?;
            let depth = self.uint_u16()?;
            self.lit(b"}")?;
            return Ok(ReducibilityHint::Regular(depth));
        }
        match self.quoted()? {
            b"abbrev" => Ok(ReducibilityHint::Abbrev),
            b"opaque" => Ok(ReducibilityHint::Opaque),
            _ => Err(Fallback),
        }
    }

    #[inline(always)]
    fn close(&mut self, l: &[u8]) -> Result<(), Fallback> {
        if self.s.len() - self.i > l.len()
            && &self.s[self.i..self.i + l.len()] == l
            && self.s[self.i + l.len()] == b'\n'
        {
            self.i += l.len() + 1;
            self.next = self.i;
            return Ok(());
        }
        self.lit(l)?;
        self.done()
    }

    #[inline(always)]
    fn done(&mut self) -> Result<(), Fallback> {
        self.next = match self.s.get(self.i) {
            None => self.i,
            Some(b'\n') => self.i + 1,
            Some(c) if c.is_ascii_whitespace() => eol_slow(self.s, self.i)?,
            Some(_) => return Err(Fallback),
        };
        Ok(())
    }
}

#[inline(never)]
fn uint_slow(s: &[u8], mut i: usize) -> Result<(u64, usize), Fallback> {
    let start = i;
    let mut x = 0u64;
    while i < s.len() {
        let d = s[i].wrapping_sub(b'0');
        if d > 9 {
            break;
        }
        x = x * 10 + u64::from(d);
        i += 1;
    }
    if i == start || i - start > 19 {
        return Err(Fallback);
    }
    Ok((x, i))
}

#[inline(never)]
fn eol_slow(s: &[u8], mut i: usize) -> Result<usize, Fallback> {
    while let Some(&c) = s.get(i) {
        match c {
            b'\n' => return Ok(i + 1),
            c if c.is_ascii_whitespace() => i += 1,
            _ => return Err(Fallback),
        }
    }
    Ok(i)
}

#[derive(Clone, Copy)]
struct ExprEntry<'a> {
    ptr: Option<ExprPtr<'a>>,
    child_mask: u64,
}

const NO_EXPR: ExprEntry<'static> = ExprEntry {
    ptr: None,
    child_mask: 0,
};

#[cold]
#[inline(never)]
fn undefined_index(kind: &str, idx: u32) -> ! {
    reject!("export references {kind} index {idx} before it is defined")
}

#[inline(always)]
fn put_at<T: Copy>(v: &mut Vec<Option<T>>, i: usize, x: T) {
    if i == v.len() {
        v.push(Some(x));
        return;
    }
    if i > v.len() {
        v.resize(i + 1, None);
    }
    v[i] = Some(x);
}

enum FastError {
    Fallback,
    Failed(Box<dyn Error>),
}

impl From<Fallback> for FastError {
    fn from(_: Fallback) -> Self {
        FastError::Fallback
    }
}

impl<'a> Parser<'a> {
    pub fn new(arena: &'a Bump, config: Config) -> Self {
        Self::with_input_len(arena, config, 0)
    }

    pub fn with_input_len(arena: &'a Bump, config: Config, input_len: usize) -> Self {
        let mut dag = Dag::new(&config, input_len);
        let anon = NamePtr::global(dag.names.intern(arena, Name::Anon));
        let zero = LevelPtr::global(dag.levels.intern(arena, Level::Zero));
        let mut names_by_idx = Vec::with_capacity(input_len / 128 + 1);
        names_by_idx.push(Some(anon));
        let mut levels_by_idx = Vec::with_capacity(input_len / 1024 + 1);
        levels_by_idx.push(Some(zero));
        Self {
            arena,
            dag,
            anon,
            zero,
            names_by_idx,
            levels_by_idx,
            exprs_by_idx: Vec::with_capacity(input_len / 48),
            declars: new_fx_index_map(),
            config,
            mutual_block_sizes: new_fx_hash_map(),
            scratch_idxs: Vec::new(),
        }
    }

    fn push_name(&mut self, expected: BackRef, n: Name<'a>) {
        ensure!(
            self.dag.names.get(&n).is_none(),
            "Attempted to insert duplicate Name"
        );
        let ptr = NamePtr::global(self.dag.names.insert(self.arena, n));
        put_at(&mut self.names_by_idx, expected.index() as usize, ptr);
    }

    fn push_level(&mut self, expected: BackRef, l: Level<'a>) {
        ensure!(
            self.dag.levels.get(&l).is_none(),
            "Attempted to insert duplicate Level"
        );
        let ptr = LevelPtr::global(self.dag.levels.insert(self.arena, l));
        put_at(&mut self.levels_by_idx, expected.index() as usize, ptr);
    }

    #[inline(always)]
    fn push_expr(&mut self, expected: BackRef, e: Expr<'a>, num_loose_bvars: u16, fv_mask: u64) {
        let r: &'a Expr<'a> = self.arena.alloc(e);
        let ptr = ExprPtr::global(r, num_loose_bvars);
        let entry = ExprEntry {
            ptr: Some(ptr),
            child_mask: fv_mask,
        };
        debug_assert_eq!(entry.child_mask, crate::term::expr::child_mask(ptr));
        let i = expected.index() as usize;
        if i == self.exprs_by_idx.len() {
            self.exprs_by_idx.push(entry);
            return;
        }
        if i > self.exprs_by_idx.len() {
            self.exprs_by_idx.resize(i + 1, NO_EXPR);
        }
        self.exprs_by_idx[i] = entry;
    }

    fn get_name_ptr(&self, idx: u32) -> NamePtr<'a> {
        match self.names_by_idx.get(idx as usize).copied().flatten() {
            Some(p) => p,
            None => undefined_index("name", idx),
        }
    }

    fn get_level_ptr(&self, idx: u32) -> LevelPtr<'a> {
        match self.levels_by_idx.get(idx as usize).copied().flatten() {
            Some(p) => p,
            None => undefined_index("level", idx),
        }
    }

    fn get_names(&self, idxs: &[u32]) -> Vec<NamePtr<'a>> {
        idxs.iter().map(|&idx| self.get_name_ptr(idx)).collect()
    }

    fn get_uparams_ptr(&mut self, name_idxs: &[u32]) -> LevelsPtr<'a> {
        let mut levels = Vec::with_capacity(name_idxs.len());
        for name_idx in name_idxs.iter().copied() {
            let name_ptr = self.get_name_ptr(name_idx);
            let hash = hash64!(crate::term::level::PARAM_HASH, name_ptr);
            let r = self.dag.levels.get(&Level::Param(name_ptr, hash)).unwrap();
            levels.push(LevelPtr::global(r));
        }
        LevelsPtr::global(self.dag.uparams.intern(self.arena, &levels))
    }

    fn get_levels_ptr(&mut self, idxs: &[u32]) -> LevelsPtr<'a> {
        let levels = idxs
            .iter()
            .map(|&idx| self.get_level_ptr(idx))
            .collect::<Vec<_>>();
        LevelsPtr::global(self.dag.uparams.intern(self.arena, &levels))
    }

    fn get_expr_ptr(&self, idx: u32) -> ExprPtr<'a> {
        self.get_expr(idx).0
    }

    fn get_expr(&self, idx: u32) -> (ExprPtr<'a>, u64) {
        match self.exprs_by_idx.get(idx as usize) {
            Some(&ExprEntry {
                ptr: Some(p),
                child_mask,
            }) => (p, child_mask),
            _ => undefined_index("expression", idx),
        }
    }

    #[inline(always)]
    fn get_body(&self, idx: u32) -> (ExprPtr<'a>, u64) {
        let (p, child_mask) = self.get_expr(idx);
        (
            p,
            crate::term::expr::under_binder(child_mask, p.num_loose_bvars()),
        )
    }

    #[inline(never)]
    fn slow_line(&mut self, input: &[u8], pos: usize) -> Result<usize, Box<dyn Error>> {
        let end = match find_newline(&input[pos..]) {
            Some(i) => pos + i + 1,
            None => input.len(),
        };
        let line = std::str::from_utf8(&input[pos..end])?;
        self.go1_general(line)?;
        Ok(end)
    }

    #[inline(never)]
    fn run_over(&mut self, input: &[u8]) -> Result<(), Box<dyn Error>> {
        let mut idxs = std::mem::take(&mut self.scratch_idxs);
        let mut pos = 0;
        let out = loop {
            if pos >= input.len() {
                break Ok(());
            }
            pos = match self.fast_line(input, pos, &mut idxs) {
                Ok(next) => next,
                Err(FastError::Failed(e)) => break Err(e),
                Err(FastError::Fallback) => match self.slow_line(input, pos) {
                    Ok(next) => next,
                    Err(e) => break Err(e),
                },
            };
        };
        self.scratch_idxs = idxs;
        out
    }

    fn finish(self) -> crate::checker::context::ExportFile<'a> {
        let name_cache = self.dag.mk_name_cache(self.anon);
        crate::checker::context::ExportFile {
            dag: self.dag,
            anon: self.anon,
            zero: self.zero,
            declars: self.declars,
            name_cache,
            config: self.config,
            mutual_block_sizes: self.mutual_block_sizes,
        }
    }

    fn fast_line(&mut self, s: &[u8], pos: usize, idxs: &mut Vec<u32>) -> Result<usize, FastError> {
        if s.len() - pos < 8 {
            return Err(FastError::Fallback);
        }
        let fast_end = s.len().saturating_sub(15);
        if s[pos + 2] != b'a' {
            return self.other_line(s, fast_end, pos, idxs);
        }
        let mut c = Cur {
            s,
            fast_end,
            i: pos,
            next: 0,
        };
        c.lit(b"{\"app\":{\"arg\":")?;
        let arg = c.uint_u32()?;
        c.lit(b",\"fn\":")?;
        let fun = c.uint_u32()?;
        c.lit(b"},\"ie\":")?;
        let i = c.uint_u32()?;
        c.close(b"}")?;
        self.do_app(BackRef::Ie(i), fun, arg);
        Ok(c.next)
    }

    #[inline(never)]
    fn other_line(
        &mut self,
        s: &[u8],
        fast_end: usize,
        pos: usize,
        idxs: &mut Vec<u32>,
    ) -> Result<usize, FastError> {
        let mut c = Cur {
            s,
            fast_end,
            i: pos,
            next: 0,
        };
        self.fast_body(&mut c, idxs)?;
        Ok(c.next)
    }

    #[inline(always)]
    fn fast_body(&mut self, c: &mut Cur<'_>, idxs: &mut Vec<u32>) -> Result<(), FastError> {
        match c.s[c.i + 2] {
            b'i' => match c.s[c.i + 3] {
                b'e' => {
                    c.lit(b"{\"ie\":")?;
                    let i = c.uint_u32()?;
                    c.lit(b",\"")?;
                    match c.peek(0)? {
                        b'l' => match c.peek(1)? {
                            b'a' => {
                                c.lit(b"lam\":{\"binderInfo\":")?;
                                c.quoted()?;
                                c.lit(b",\"body\":")?;
                                let body = c.uint_u32()?;
                                c.lit(b",\"name\":")?;
                                c.uint_u32()?;
                                c.lit(b",\"type\":")?;
                                let binder_type = c.uint_u32()?;
                                c.close(b"}}")?;
                                self.do_lambda(BackRef::Ie(i), binder_type, body);
                                Ok(())
                            }
                            b'e' => {
                                c.lit(b"letE\":{\"body\":")?;
                                let body = c.uint_u32()?;
                                c.lit(b",\"name\":")?;
                                c.uint_u32()?;
                                c.lit(b",\"nondep\":")?;
                                let nondep = c.boolean()?;
                                c.lit(b",\"type\":")?;
                                let binder_type = c.uint_u32()?;
                                c.lit(b",\"value\":")?;
                                let val = c.uint_u32()?;
                                c.close(b"}}")?;
                                self.do_let(BackRef::Ie(i), binder_type, val, body, nondep);
                                Ok(())
                            }
                            _ => Err(FastError::Fallback),
                        },
                        b'n' => {
                            c.lit(b"natVal\":")?;
                            let digits = c.quoted()?;
                            c.close(b"}")?;
                            let big = BigUint::parse_bytes(digits, 10).ok_or_else(|| {
                                FastError::Failed(Box::from(
                                    "invalid BigUint decimal string".to_string(),
                                ))
                            })?;
                            self.do_nat_lit(BackRef::Ie(i), big)
                                .map_err(FastError::Failed)
                        }
                        b'p' => {
                            c.lit(b"proj\":{\"idx\":")?;
                            let idx = c.uint_usize()?;
                            c.lit(b",\"struct\":")?;
                            let structure = c.uint_u32()?;
                            c.lit(b",\"typeName\":")?;
                            let ty_name = c.uint_u32()?;
                            c.close(b"}}")?;
                            self.do_proj(BackRef::Ie(i), ty_name, idx, structure);
                            Ok(())
                        }
                        b's' => match c.peek(1)? {
                            b'o' => {
                                c.lit(b"sort\":")?;
                                let level = c.uint_u32()?;
                                c.close(b"}")?;
                                self.do_sort(BackRef::Ie(i), level);
                                Ok(())
                            }
                            b't' => {
                                c.lit(b"strVal\":")?;
                                let string = c.quoted_str()?;
                                c.close(b"}")?;
                                self.do_str_lit(BackRef::Ie(i), string)
                                    .map_err(FastError::Failed)
                            }
                            _ => Err(FastError::Fallback),
                        },
                        _ => Err(FastError::Fallback),
                    }
                }
                b'l' => {
                    c.lit(b"{\"il\":")?;
                    let i = c.uint_u32()?;
                    c.lit(b",\"")?;
                    match c.peek(0)? {
                        b'i' => {
                            c.lit(b"imax\":[")?;
                            let l = c.uint_u32()?;
                            c.lit(b",")?;
                            let r = c.uint_u32()?;
                            c.close(b"]}")?;
                            self.do_imax(BackRef::Il(i), l, r);
                            Ok(())
                        }
                        b'm' => {
                            c.lit(b"max\":[")?;
                            let l = c.uint_u32()?;
                            c.lit(b",")?;
                            let r = c.uint_u32()?;
                            c.close(b"]}")?;
                            self.do_max(BackRef::Il(i), l, r);
                            Ok(())
                        }
                        b'p' => {
                            c.lit(b"param\":")?;
                            let n = c.uint_u32()?;
                            c.close(b"}")?;
                            self.do_level_param(BackRef::Il(i), n);
                            Ok(())
                        }
                        b's' => {
                            c.lit(b"succ\":")?;
                            let l = c.uint_u32()?;
                            c.close(b"}")?;
                            self.do_succ(BackRef::Il(i), l);
                            Ok(())
                        }
                        _ => Err(FastError::Fallback),
                    }
                }
                b'n' => {
                    c.lit(b"{\"in\":")?;
                    let i = c.uint_u32()?;
                    c.lit(b",\"")?;
                    match c.peek(0)? {
                        b'n' => {
                            c.lit(b"num\":{\"i\":")?;
                            let n = c.uint_u32()?;
                            c.lit(b",\"pre\":")?;
                            let pre = c.uint_u32()?;
                            c.close(b"}}")?;
                            self.do_name_num(BackRef::In(i), pre, u64::from(n));
                            Ok(())
                        }
                        b's' => {
                            c.lit(b"str\":{\"pre\":")?;
                            let pre = c.uint_u32()?;
                            c.lit(b",\"str\":")?;
                            let string = c.quoted_str()?;
                            c.close(b"}}")?;
                            self.do_name_str(BackRef::In(i), pre, string);
                            Ok(())
                        }
                        _ => Err(FastError::Fallback),
                    }
                }
                _ => Err(FastError::Fallback),
            },
            b'b' => {
                c.lit(b"{\"bvar\":")?;
                let dbj_idx = c.uint_u16()?;
                c.lit(b",\"ie\":")?;
                let i = c.uint_u32()?;
                c.close(b"}")?;
                self.do_bvar(BackRef::Ie(i), dbj_idx)
                    .map_err(FastError::Failed)
            }
            b'c' => {
                c.lit(b"{\"const\":{\"name\":")?;
                let name = c.uint_u32()?;
                c.lit(b",\"us\":")?;
                c.u32_array(idxs)?;
                c.lit(b"},\"ie\":")?;
                let i = c.uint_u32()?;
                c.close(b"}")?;
                self.do_const(BackRef::Ie(i), name, idxs);
                Ok(())
            }
            b'd' => {
                c.lit(b"{\"def\":{\"all\":")?;
                c.skip_u32_array()?;
                c.lit(b",\"hints\":")?;
                let hint = c.hint()?;
                c.lit(b",\"levelParams\":")?;
                c.u32_array(idxs)?;
                c.lit(b",\"name\":")?;
                let name = c.uint_u32()?;
                c.lit(b",\"safety\":\"safe\",\"type\":")?;
                let ty = c.uint_u32()?;
                c.lit(b",\"value\":")?;
                let val = c.uint_u32()?;
                c.close(b"}}")?;
                self.do_def(name, ty, val, idxs, hint);
                Ok(())
            }
            b'f' => {
                c.lit(b"{\"forallE\":{\"binderInfo\":")?;
                c.quoted()?;
                c.lit(b",\"body\":")?;
                let body = c.uint_u32()?;
                c.lit(b",\"name\":")?;
                c.uint_u32()?;
                c.lit(b",\"type\":")?;
                let binder_type = c.uint_u32()?;
                c.lit(b"},\"ie\":")?;
                let i = c.uint_u32()?;
                c.close(b"}")?;
                self.do_pi(BackRef::Ie(i), binder_type, body);
                Ok(())
            }
            b't' => {
                c.lit(b"{\"thm\":{\"all\":")?;
                c.skip_u32_array()?;
                c.lit(b",\"levelParams\":")?;
                c.u32_array(idxs)?;
                c.lit(b",\"name\":")?;
                let name = c.uint_u32()?;
                c.lit(b",\"type\":")?;
                let ty = c.uint_u32()?;
                c.lit(b",\"value\":")?;
                let val = c.uint_u32()?;
                c.close(b"}}")?;
                self.do_thm(name, ty, val, idxs);
                Ok(())
            }
            _ => Err(FastError::Fallback),
        }
    }

    #[inline]
    fn intern_str(&mut self, s: &str) -> StringPtr<'a> {
        if let Some(r) = self.dag.strings.get(s) {
            return StringPtr::global(r);
        }
        let owned = Cow::Borrowed(&*self.arena.alloc_str(s));
        StringPtr::global(self.dag.strings.insert(self.arena, owned))
    }

    #[inline]
    fn do_name_str(&mut self, idx: BackRef, pre: u32, s: &str) {
        let pfx = self.get_name_ptr(pre);
        let sfx = self.intern_str(s);
        let hash = hash64!(crate::term::name::STR_HASH, pfx, sfx);
        self.push_name(idx, Name::Str(pfx, sfx, hash));
    }

    #[inline]
    fn do_name_num(&mut self, idx: BackRef, pre: u32, sfx: u64) {
        let pfx = self.get_name_ptr(pre);
        let hash = hash64!(crate::term::name::NUM_HASH, pfx, sfx);
        self.push_name(idx, Name::Num(pfx, sfx, hash));
    }

    #[inline]
    fn do_nat_lit(&mut self, idx: BackRef, big_uint: BigUint) -> Result<(), Box<dyn Error>> {
        if !self.config.nat_extension {
            return decline(
                "Nat lit extension disallowed by checker execution config, but export file contains a nat literal",
            );
        }
        let num_ptr = BigUintPtr::global(
            self.dag
                .bignums
                .as_mut()
                .unwrap()
                .intern(self.arena, big_uint),
        );
        let hash = hash64!(crate::term::expr::NAT_LIT_HASH, num_ptr);
        self.push_expr(idx, Expr::NatLit { ptr: num_ptr, hash }, 0, 0);
        Ok(())
    }

    #[inline]
    fn do_str_lit(&mut self, idx: BackRef, s: &str) -> Result<(), Box<dyn Error>> {
        if !self.config.string_extension {
            return decline(
                "String lit extension disallowed by checker execution config, but export file contains a string literal",
            );
        }
        let string_ptr = self.intern_str(s);
        let hash = hash64!(crate::term::expr::STRING_LIT_HASH, string_ptr);
        self.push_expr(
            idx,
            Expr::StringLit {
                ptr: string_ptr,
                hash,
            },
            0,
            0,
        );
        Ok(())
    }

    #[inline]
    fn do_succ(&mut self, idx: BackRef, l: u32) {
        let l = self.get_level_ptr(l);
        let hash = hash64!(crate::term::level::SUCC_HASH, l);
        self.push_level(idx, Level::Succ(l, hash));
    }

    #[inline]
    fn do_max(&mut self, idx: BackRef, l: u32, r: u32) {
        let l = self.get_level_ptr(l);
        let r = self.get_level_ptr(r);
        let hash = hash64!(crate::term::level::MAX_HASH, l, r);
        self.push_level(idx, Level::Max(l, r, hash));
    }

    #[inline]
    fn do_imax(&mut self, idx: BackRef, l: u32, r: u32) {
        let l = self.get_level_ptr(l);
        let r = self.get_level_ptr(r);
        let hash = hash64!(crate::term::level::IMAX_HASH, l, r);
        self.push_level(idx, Level::IMax(l, r, hash));
    }

    #[inline]
    fn do_level_param(&mut self, idx: BackRef, n: u32) {
        let n = self.get_name_ptr(n);
        let hash = hash64!(crate::term::level::PARAM_HASH, n);
        self.push_level(idx, Level::Param(n, hash));
    }

    #[inline]
    fn do_sort(&mut self, idx: BackRef, level: u32) {
        let level = self.get_level_ptr(level);
        let hash = hash64!(crate::term::expr::SORT_HASH, level);
        self.push_expr(idx, Expr::Sort { level, hash }, 0, 0);
    }

    #[inline]
    fn do_const(&mut self, idx: BackRef, name: u32, us: &[u32]) {
        let name = self.get_name_ptr(name);
        let levels = self.get_levels_ptr(us);
        let hash = hash64!(crate::term::expr::CONST_HASH, name, levels);
        self.push_expr(idx, Expr::Const { name, levels, hash }, 0, 0);
    }

    #[inline]
    fn do_app(&mut self, idx: BackRef, fun: u32, arg: u32) {
        let (fun, fun_mask) = self.get_expr(fun);
        let (arg, arg_mask) = self.get_expr(arg);
        let hash = hash64!(crate::term::expr::APP_HASH, fun, arg);
        let fv_mask = fun_mask | arg_mask;
        let nlb = fun.num_loose_bvars().max(arg.num_loose_bvars());
        self.push_expr(
            idx,
            Expr::App {
                fun,
                arg,
                fv_mask,
                hash,
            },
            nlb,
            fv_mask,
        );
    }

    #[inline]
    fn do_bvar(&mut self, idx: BackRef, dbj_idx: u16) -> Result<(), Box<dyn Error>> {
        if dbj_idx == u16::MAX {
            return decline("bvar index exceeds implementation limit");
        }
        let hash = hash64!(crate::term::expr::VAR_HASH, dbj_idx);
        let fv_mask = crate::term::expr::var_mask(dbj_idx);
        self.push_expr(idx, Expr::Var { dbj_idx, hash }, dbj_idx + 1, fv_mask);
        Ok(())
    }

    #[inline]
    fn do_lambda(&mut self, idx: BackRef, binder_type: u32, body: u32) {
        let (binder_type, binder_type_mask) = self.get_expr(binder_type);
        let (body, body_mask) = self.get_body(body);
        let hash = hash64!(crate::term::expr::LAMBDA_HASH, binder_type, body);
        let fv_mask = binder_type_mask | body_mask;
        let nlb = binder_type
            .num_loose_bvars()
            .max(body.num_loose_bvars().saturating_sub(1));
        self.push_expr(
            idx,
            Expr::Lambda {
                binder_type,
                body,
                fv_mask,
                hash,
            },
            nlb,
            fv_mask,
        );
    }

    #[inline]
    fn do_pi(&mut self, idx: BackRef, binder_type: u32, body: u32) {
        let (binder_type, binder_type_mask) = self.get_expr(binder_type);
        let (body, body_mask) = self.get_body(body);
        let hash = hash64!(crate::term::expr::PI_HASH, binder_type, body);
        let fv_mask = binder_type_mask | body_mask;
        let nlb = binder_type
            .num_loose_bvars()
            .max(body.num_loose_bvars().saturating_sub(1));
        self.push_expr(
            idx,
            Expr::Pi {
                binder_type,
                body,
                fv_mask,
                hash,
            },
            nlb,
            fv_mask,
        );
    }

    #[inline]
    fn do_let(&mut self, idx: BackRef, ty: u32, value: u32, body: u32, nondep: bool) {
        let (binder_type, binder_type_mask) = self.get_expr(ty);
        let (val, val_mask) = self.get_expr(value);
        let (body, body_mask) = self.get_body(body);
        let hash = hash64!(crate::term::expr::LET_HASH, binder_type, val, body, nondep);
        let fv_mask = binder_type_mask | val_mask | body_mask;
        let nlb = binder_type.num_loose_bvars().max(
            val.num_loose_bvars()
                .max(body.num_loose_bvars().saturating_sub(1)),
        );
        self.push_expr(
            idx,
            Expr::Let {
                data: self.arena.alloc(crate::term::expr::LetData {
                    binder_type,
                    val,
                    body,
                    nondep,
                }),
                fv_mask,
                hash,
            },
            nlb,
            fv_mask,
        );
    }

    #[inline]
    fn do_proj(&mut self, idx: BackRef, type_name: u32, proj_idx: usize, struct_: u32) {
        let proj_idx = u16::try_from(proj_idx).expect("projection index does not fit in u16");
        let ty_name = self.get_name_ptr(type_name);
        let (structure, fv_mask) = self.get_expr(struct_);
        let hash = hash64!(crate::term::expr::PROJ_HASH, ty_name, proj_idx, structure);
        self.push_expr(
            idx,
            Expr::Proj {
                ty_name,
                idx: proj_idx,
                structure,
                fv_mask,
                hash,
            },
            structure.num_loose_bvars(),
            fv_mask,
        );
    }

    fn add_declar(&mut self, name: NamePtr<'a>, d: Declar<'a>) {
        let idx = u32::try_from(self.declars.len()).expect("declaration count exceeds u32");
        if idx == crate::term::name::NO_DECL {
            unsupported!("declaration count exceeds u32");
        }
        ensure!(self.declars.insert(name, d).is_none());
        name.as_ref().set_decl_idx(idx);
    }

    #[inline]
    fn do_def(&mut self, name: u32, ty: u32, value: u32, uparams: &[u32], hint: ReducibilityHint) {
        let name = self.get_name_ptr(name);
        let ty = self.get_expr_ptr(ty);
        let val = self.get_expr_ptr(value);
        let uparams = self.get_uparams_ptr(uparams);
        let info = DeclarInfo { name, uparams, ty };
        let definition = Declar::Definition { info, val, hint };
        self.add_declar(name, definition);
    }

    #[inline]
    fn do_thm(&mut self, name: u32, ty: u32, value: u32, uparams: &[u32]) {
        let name = self.get_name_ptr(name);
        let ty = self.get_expr_ptr(ty);
        let val = self.get_expr_ptr(value);
        let uparams = self.get_uparams_ptr(uparams);
        let info = DeclarInfo { name, uparams, ty };
        let theorem = Declar::Theorem { info, val };
        self.add_declar(name, theorem);
    }

    fn go1_general(&mut self, line: &str) -> Result<(), Box<dyn Error>> {
        use ExportJsonVal::{
            Axiom, Defn, ExprApp, ExprBVar, ExprConst, ExprLambda, ExprLet, ExprMData, ExprPi,
            ExprProj, ExprSort, Inductive, LevelIMax, LevelMax, LevelParam, LevelSucc, Metadata,
            NameNum, NameStr, NatLit, Opaque, Quot, StrLit, Thm,
        };
        let ExportJsonObject {
            val,
            i: assigned_idx,
        } = serde_json::from_str::<ExportJsonObject>(line)?;
        match val {
            Metadata(json_val) => {
                check_semver(&json_val)?;
            }
            NameStr { pre, str } => self.do_name_str(assigned_idx.unwrap(), pre, &str),
            NameNum { pre, i } => self.do_name_num(assigned_idx.unwrap(), pre, u64::from(i)),
            NatLit(big_uint) => self.do_nat_lit(assigned_idx.unwrap(), big_uint)?,
            StrLit(cow_str) => self.do_str_lit(assigned_idx.unwrap(), &cow_str)?,
            LevelSucc(l) => self.do_succ(assigned_idx.unwrap(), l),
            LevelMax([l, r]) => self.do_max(assigned_idx.unwrap(), l, r),
            LevelIMax([l, r]) => self.do_imax(assigned_idx.unwrap(), l, r),
            LevelParam(var_idx) => self.do_level_param(assigned_idx.unwrap(), var_idx),
            ExprSort(level) => self.do_sort(assigned_idx.unwrap(), level),
            ExprMData { .. } => return decline("Expr.mdata is not supported"),
            ExprConst { name, levels } => self.do_const(assigned_idx.unwrap(), name, &levels),
            ExprApp { fun, arg } => self.do_app(assigned_idx.unwrap(), fun, arg),
            ExprBVar(dbj_idx) => self.do_bvar(assigned_idx.unwrap(), dbj_idx)?,
            ExprLambda { binder_type, body } => {
                self.do_lambda(assigned_idx.unwrap(), binder_type, body);
            }
            ExprPi { binder_type, body } => self.do_pi(assigned_idx.unwrap(), binder_type, body),
            ExprLet {
                ty,
                value,
                body,
                nondep,
            } => self.do_let(assigned_idx.unwrap(), ty, value, body, nondep),
            ExprProj {
                type_name,
                idx,
                structure: struct_,
            } => self.do_proj(assigned_idx.unwrap(), type_name, idx, struct_),
            Axiom {
                name,
                ty,
                uparams,
                is_unsafe,
            } => {
                if is_unsafe {
                    return decline("unsafe declarations are not supported");
                }
                let name = self.get_name_ptr(name);
                let uparams = self.get_uparams_ptr(&uparams);
                let ty = self.get_expr_ptr(ty);
                let info = DeclarInfo { name, uparams, ty };
                let axiom = Declar::Axiom { info };
                let name_string = name.to_string();
                match self.config.axiom_policy.decision(&name_string) {
                    AxiomDecision::Allow | AxiomDecision::Warn => self.add_declar(name, axiom),
                    AxiomDecision::Reject => {
                        return Err(format!(
                            "export file declares disallowed axiom {name_string:?}"
                        )
                        .into());
                    }
                }
            }
            Defn {
                name,
                ty,
                uparams,
                value,
                hint,
                safety,
            } => {
                if matches!(safety, DefinitionSafety::Unsafe | DefinitionSafety::Partial) {
                    return decline("unsafe and partial definitions are not supported");
                }
                self.do_def(name, ty, value, &uparams, hint);
            }
            Thm {
                name,
                ty,
                uparams,
                value,
            } => self.do_thm(name, ty, value, &uparams),
            Opaque {
                name,
                ty,
                uparams,
                value,
                is_unsafe,
            } => {
                if is_unsafe {
                    return decline("unsafe declarations are not supported");
                }
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let val = self.get_expr_ptr(value);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, uparams, ty };
                let definition = Declar::Opaque { info, val };
                self.add_declar(name, definition);
            }
            Quot {
                name, ty, uparams, ..
            } => {
                let name = self.get_name_ptr(name);
                let ty = self.get_expr_ptr(ty);
                let uparams = self.get_uparams_ptr(&uparams);
                let info = DeclarInfo { name, uparams, ty };
                let quot = Declar::Quot { info };
                self.add_declar(name, quot);
            }
            Inductive {
                ind_vals,
                ctor_vals,
                rec_vals,
            } => {
                let block_start = self.declars.len();
                let block_size = ind_vals.len() + ctor_vals.len() + rec_vals.len();
                let listed_ctors: Vec<(u32, u32)> = ind_vals
                    .iter()
                    .flat_map(|ind| ind.ctors.iter().map(move |&ctor| (ctor, ind.name)))
                    .collect();
                for IndInfo {
                    name,
                    ty,
                    uparams,
                    all,
                    ctors,
                    is_rec,
                    num_nested,
                    num_params,
                    num_indices,
                    is_unsafe,
                    ..
                } in ind_vals
                {
                    if is_unsafe {
                        return decline("unsafe declarations are not supported");
                    }
                    let name = self.get_name_ptr(name);
                    self.mutual_block_sizes
                        .insert(name, (block_start, block_size));
                    let uparams = self.get_uparams_ptr(&uparams);
                    let ty = self.get_expr_ptr(ty);
                    let all_ind_names = Arc::from(self.get_names(&all));
                    let all_ctor_names = Arc::from(self.get_names(&ctors));
                    let inductive = Declar::Inductive(InductiveData {
                        info: DeclarInfo { name, uparams, ty },
                        is_recursive: is_rec,
                        is_nested: num_nested > 0,
                        num_params,
                        num_indices,
                        all_ind_names,
                        all_ctor_names,
                    });
                    self.add_declar(name, inductive);
                }
                for Constructor {
                    name,
                    uparams,
                    ty,
                    is_unsafe,
                    induct,
                    cidx,
                    num_params,
                    num_fields,
                    ..
                } in ctor_vals
                {
                    if is_unsafe {
                        return decline("unsafe declarations are not supported");
                    }
                    if !listed_ctors.contains(&(name, induct)) {
                        return Err(
                            "constructor is not listed by its inductive type in this block".into(),
                        );
                    }
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, uparams, ty };
                    let parent_inductive = self.get_name_ptr(induct);
                    let ctor_idx = cidx;
                    let ctor = Declar::Constructor(ConstructorData {
                        info,
                        inductive_name: parent_inductive,
                        ctor_idx,
                        num_params,
                        num_fields,
                    });
                    self.add_declar(name, ctor);
                }
                for Recursor {
                    name,
                    uparams,
                    ty,
                    rules,
                    is_unsafe,
                    num_params,
                    num_indices,
                    num_motives,
                    num_minors,
                    k,
                    all,
                    ..
                } in rec_vals
                {
                    if is_unsafe {
                        return decline("unsafe declarations are not supported");
                    }
                    let name = self.get_name_ptr(name);
                    let ty = self.get_expr_ptr(ty);
                    let uparams = self.get_uparams_ptr(&uparams);
                    let info = DeclarInfo { name, uparams, ty };
                    let rules = rules
                        .into_iter()
                        .map(
                            |RecursorRule { rhs, ctor, nfields }| crate::checker::env::RecRule {
                                val: self.get_expr_ptr(rhs),
                                ctor_name: self.get_name_ptr(ctor),
                                ctor_telescope_size_wo_params: nfields,
                            },
                        )
                        .collect::<Vec<_>>();
                    let all_inductives = self.get_names(&all);
                    let recursor = Declar::Recursor(RecursorData {
                        info,
                        all_inductives: Arc::from(all_inductives),
                        num_params,
                        num_indices,
                        num_motives,
                        num_minors,
                        rec_rules: Arc::from(rules),
                        is_k: k,
                    });
                    self.add_declar(name, recursor);
                }
            }
        }
        Ok(())
    }
}

/// Needed because the lean4export format serializes nat literals as strings:
/// <https://github.com/leanprover/lean4export/blob/ddeb0869b0b5679b0104e16291ffd929fbaa6a48/format_ndjson.md?plain=1#L186>
fn deserialize_biguint_from_string<'de, D>(deserializer: D) -> Result<BigUint, D::Error>
where
    D: Deserializer<'de>,
{
    use std::str::FromStr;
    struct BigUintStringVisitor;

    impl Visitor<'_> for BigUintStringVisitor {
        type Value = BigUint;

        fn expecting(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
            f.write_str("a string containing a natural number")
        }

        fn visit_str<E>(self, v: &str) -> Result<BigUint, E>
        where
            E: DeError,
        {
            BigUint::from_str(v)
                .map_err(|e| E::custom(format!("invalid BigUint decimal string: {e}")))
        }

        fn visit_string<E>(self, v: String) -> Result<BigUint, E>
        where
            E: DeError,
        {
            self.visit_str(&v)
        }
    }
    deserializer.deserialize_str(BigUintStringVisitor)
}

#[cfg(test)]
mod tests;
