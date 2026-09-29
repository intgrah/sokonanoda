use crate::parser::parse_export_file;
use crate::util::{Config, CowStr, ExportFile, LevelPtr, TcCtx};
use rand::distributions::Alphanumeric;
use rand::{rngs::ThreadRng, Rng};
use std::error::Error;
use stumpalo::Arena;

fn empty_test_config() -> Config {
    Config {
        export_file_path: None,
        use_stdin: false,
        permitted_axioms: Some(Vec::new()),
        permit_standard_axioms: false,
        unpermitted_axiom_hard_error: true,
        parse_only: false,
        nat_extension: false,
        string_extension: false,
        num_threads: 1,
        print_success_message: false,
        print_axioms: false,
        unsafe_permit_all_axioms: false,
    }
}

pub(crate) fn test_export_file<A>(f: impl FnOnce(&ExportFile) -> A) -> Result<A, Box<dyn Error>> {
    let arena = Arena::new();
    let (export_file, _) = parse_export_file(arena.as_arena_ref(), std::io::empty(), empty_test_config())?;
    Ok(f(&export_file))
}

pub(crate) fn test_export_file_should_panic<A>(f: impl FnOnce(&ExportFile) -> A) {
    test_export_file(f).expect("create empty test environment");
}

pub(crate) fn test_ctx<'p, A>(f: impl FnOnce(&mut TcCtx) -> A) -> Result<A, Box<dyn Error>> {
    test_export_file(|export_file| export_file.with_ctx(|ctx, _cache, _arena| f(ctx)))
}

impl<'t, 'p: 't> TcCtx<'t, 'p> {
    #[cfg(test)]
    pub(crate) fn level_n(&mut self, mut l: LevelPtr<'t>, n: u64) -> LevelPtr<'t> {
        for _ in 0..n {
            l = self.succ(l);
        }
        l
    }

    #[cfg(test)]
    pub(crate) fn param_quick(&mut self, s: &'static str) -> LevelPtr<'t> {
        let n = self.str1(&s);
        self.param(n)
    }
}

#[test]
#[should_panic(expected = "expected a sort")]
fn reject_is_prop_when_inferred_type_is_not_a_sort() {
    test_export_file_should_panic(|export| {
        export.with_tc(crate::env::EnvLimit::Empty, |tc| {
            let sort = crate::value::mk_sort(tc.arena, tc.ctx.zero());
            let stuck_type = tc.mk_bvar_hc(0, sort);
            let malformed_type = tc.mk_bvar_hc(1, stuck_type);
            tc.is_prop_type(0, malformed_type);
        });
    })
}

#[test]
#[should_panic(expected = "inductive occurrence is not applied uniformly")]
fn reject_nonuniform_inductive_occurrence_before_reduction() {
    test_export_file_should_panic(|export| {
        export.with_ctx(|ctx, _cache, _arena| {
            let ind_name = ctx.str1("E");
            let levels = ctx.alloc_levels_slice(&[]);
            let ind = ctx.mk_const(ind_name, levels);
            let prop = ctx.prop();
            let bad_occurrence = ctx.mk_app(ind, prop);
            let one = ctx.succ(ctx.zero());
            let param_type = ctx.mk_sort(one);
            let ctor_type = ctx.mk_pi(param_type, bad_occurrence);

            ctx.check_uniform_inductive_occurrences(ctor_type, &[ind_name], levels, 1);
        });
    });
}

pub(crate) fn rand_string<'t>(rng: &mut ThreadRng, size: usize) -> CowStr<'t> {
    let rand_string: String = rng.sample_iter(&Alphanumeric).take(size).map(char::from).collect();
    CowStr::Owned(rand_string)
}

#[test]
fn hash_test0() -> Result<(), Box<dyn Error>> {
    use crate::hash64;
    use num_bigint::RandBigInt;
    use rand::thread_rng;
    test_export_file(|export| {
        let mut rng = thread_rng();
        export.with_ctx(|ctx, _cache, _arena| {
            for size in 0..100 {
                for _ in 0..100 {
                    let s = rand_string(&mut rng, size);
                    let (l, r) = (ctx.mk_string_lit_quick(s.clone()), ctx.mk_string_lit_quick(s));
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
                for _ in 0..100 {
                    let s = rng.gen_biguint(size as u64);
                    let (l, r) = (ctx.mk_nat_lit_quick(s.clone()), ctx.mk_nat_lit_quick(s));
                    assert_eq!(hash64!(l), hash64!(r));
                    assert_eq!(l, r)
                }
            }
        })
    })
}
