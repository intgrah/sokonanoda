// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use super::*;
use bumpalo::Bump;

fn config() -> Config {
    Config {
        use_stdin: true,
        ..Config::default()
    }
}

#[test]
fn ignore_binder_metadata_in_both_parser_paths() {
    let arena = Bump::new();
    let mut parser = Parser::new(&arena, &b""[..], config());
    parser.do_sort(BackRef::Ie(0), 0);
    parser.do_bvar(BackRef::Ie(1), 0).unwrap();
    parser.do_bvar(BackRef::Ie(2), 1).unwrap();
    let mut idxs = Vec::new();
    for kind in ["lam", "forallE", "letE"] {
        let mut reference: Option<ExprPtr<'_>> = None;
        for (i, style) in ["default", "implicit", "strictImplicit", "instImplicit"]
            .iter()
            .enumerate()
        {
            // These names do not exist. Binder names must never be resolved as references.
            let name = u32::MAX - u32::try_from(i).unwrap();
            let fields = if kind == "letE" {
                format!(r#""body":2,"name":{name},"nondep":false,"type":0,"value":1"#)
            } else {
                format!(r#""binderInfo":"{style}","body":2,"name":{name},"type":0"#)
            };
            let fast = if kind == "forallE" {
                format!("{{\"{kind}\":{{{fields}}},\"ie\":3}}\n")
            } else {
                format!("{{\"ie\":3,\"{kind}\":{{{fields}}}}}\n")
            };
            assert!(
                matches!(parser.fast_line(fast.as_bytes(), 0, &mut idxs), Ok(n) if n == fast.len())
            );
            let parsed = parser.get_expr_ptr(3);
            let slow = format!("{{ \"ie\":4, \"{kind}\":{{{fields}}} }}");
            parser.go1_general(&slow).unwrap();
            assert_eq!(parsed.as_ref(), parser.get_expr_ptr(4).as_ref());
            assert_eq!(parsed.num_loose_bvars(), 1);
            assert_eq!(crate::term::expr::child_mask(parsed), 1);
            if let Some(reference) = reference {
                assert_eq!(reference.as_ref(), parsed.as_ref());
            } else {
                reference = Some(parsed);
            }
        }
        // The general parser also ignores absent metadata or metadata with arbitrary JSON values.
        let fields = if kind == "letE" {
            r#""body":2,"nondep":false,"type":0,"value":1"#
        } else {
            r#""body":2,"type":0"#
        };
        let reference = parser.get_expr_ptr(3);
        for metadata in ["", r#", "name":{"ignored":true}, "binderInfo":[null]"#] {
            parser
                .go1_general(&format!("{{\"ie\":4,\"{kind}\":{{{fields}{metadata}}}}}"))
                .unwrap();
            assert_eq!(reference.as_ref(), parser.get_expr_ptr(4).as_ref());
        }
        // Domain and body references still distinguish expressions.
        parser
            .go1_general(
                &format!("{{\"ie\":4,\"{kind}\":{{{fields}}}}}")
                    .replace("\"body\":2", "\"body\":1"),
            )
            .unwrap();
        assert_ne!(reference.as_ref(), parser.get_expr_ptr(4).as_ref());
        parser
            .go1_general(
                &format!("{{\"ie\":4,\"{kind}\":{{{fields}}}}}")
                    .replace("\"type\":0", "\"type\":2"),
            )
            .unwrap();
        assert_ne!(reference.as_ref(), parser.get_expr_ptr(4).as_ref());
    }
}

#[test]
fn reject_undefined_binder_type() {
    let arena = Bump::new();
    let mut parser = Parser::new(&arena, &b""[..], config());
    parser.do_sort(BackRef::Ie(0), 0);
    let payload = std::panic::catch_unwind(std::panic::AssertUnwindSafe(|| {
        parser
            .go1_general(r#"{"ie":1,"lam":{"type":99,"body":0}}"#)
            .unwrap();
    }))
    .unwrap_err();
    let rejection = payload
        .downcast::<crate::outcome::Rejection>()
        .expect("expected a rejection");
    assert_eq!(
        rejection.0,
        "export references expression index 99 before it is defined"
    );
}
