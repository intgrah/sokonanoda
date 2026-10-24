// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

use crate::checker::context::ExportFile;
use crate::checker::env::Declar;
use crate::config::Config;
use crate::frontend::parser::parse_export_mapped;
use crate::outcome::CheckError;
use std::sync::Arc;

const NESTED_EXPORT: &str = r#"{"in":1,"str":{"pre":0,"str":"C"}}
{"il":1,"succ":0}
{"ie":0,"sort":1}
{"forallE":{"body":0,"type":0},"ie":1}
{"in":2,"str":{"pre":1,"str":"c"}}
{"bvar":0,"ie":2}
{"const":{"name":1,"us":[]},"ie":3}
{"bvar":1,"ie":4}
{"app":{"arg":4,"fn":3},"ie":5}
{"forallE":{"body":5,"type":2},"ie":6}
{"forallE":{"body":6,"type":0},"ie":7}
{"in":3,"str":{"pre":0,"str":"u"}}
{"il":2,"param":3}
{"in":4,"str":{"pre":1,"str":"rec"}}
{"app":{"arg":2,"fn":3},"ie":8}
{"ie":9,"sort":2}
{"forallE":{"body":9,"type":8},"ie":10}
{"const":{"name":2,"us":[]},"ie":11}
{"bvar":2,"ie":12}
{"app":{"arg":12,"fn":11},"ie":13}
{"app":{"arg":2,"fn":13},"ie":14}
{"app":{"arg":14,"fn":4},"ie":15}
{"forallE":{"body":15,"type":4},"ie":16}
{"app":{"arg":12,"fn":3},"ie":17}
{"app":{"arg":2,"fn":12},"ie":18}
{"forallE":{"body":18,"type":17},"ie":19}
{"forallE":{"body":19,"type":16},"ie":20}
{"forallE":{"body":20,"type":10},"ie":21}
{"forallE":{"body":21,"type":0},"ie":22}
{"app":{"arg":2,"fn":4},"ie":23}
{"ie":24,"lam":{"body":23,"type":12}}
{"ie":25,"lam":{"body":24,"type":16}}
{"ie":26,"lam":{"body":25,"type":10}}
{"ie":27,"lam":{"body":26,"type":0}}
{"inductive":{"ctors":[{"cidx":0,"induct":1,"isUnsafe":false,"levelParams":[],"name":2,"numFields":1,"numParams":1,"type":7}],"recs":[{"all":[1],"isUnsafe":false,"k":false,"levelParams":[3],"name":4,"numIndices":0,"numMinors":1,"numMotives":1,"numParams":1,"rules":[{"ctor":2,"nfields":1,"rhs":27}],"type":22}],"types":[{"all":[1],"ctors":[2],"isRec":false,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":1,"numIndices":0,"numNested":0,"numParams":1,"type":1}]}}
{"in":5,"str":{"pre":0,"str":"T"}}
{"in":6,"str":{"pre":5,"str":"base"}}
{"in":7,"str":{"pre":5,"str":"mk"}}
{"const":{"name":5,"us":[]},"ie":28}
{"app":{"arg":28,"fn":3},"ie":29}
{"forallE":{"body":28,"type":29},"ie":30}
{"in":8,"str":{"pre":5,"str":"rec"}}
{"forallE":{"body":9,"type":28},"ie":31}
{"forallE":{"body":9,"type":29},"ie":32}
{"const":{"name":6,"us":[]},"ie":33}
{"app":{"arg":33,"fn":4},"ie":34}
{"bvar":4,"ie":35}
{"const":{"name":7,"us":[]},"ie":36}
{"app":{"arg":4,"fn":36},"ie":37}
{"app":{"arg":37,"fn":35},"ie":38}
{"forallE":{"body":38,"type":18},"ie":39}
{"forallE":{"body":39,"type":29},"ie":40}
{"app":{"arg":2,"fn":35},"ie":41}
{"app":{"arg":28,"fn":11},"ie":42}
{"app":{"arg":4,"fn":42},"ie":43}
{"app":{"arg":43,"fn":35},"ie":44}
{"forallE":{"body":44,"type":41},"ie":45}
{"forallE":{"body":45,"type":28},"ie":46}
{"bvar":5,"ie":47}
{"app":{"arg":2,"fn":47},"ie":48}
{"forallE":{"body":48,"type":28},"ie":49}
{"forallE":{"body":49,"type":46},"ie":50}
{"forallE":{"body":50,"type":40},"ie":51}
{"forallE":{"body":51,"type":34},"ie":52}
{"forallE":{"body":52,"type":32},"ie":53}
{"forallE":{"body":53,"type":31},"ie":54}
{"ie":55,"lam":{"body":12,"type":46}}
{"ie":56,"lam":{"body":55,"type":40}}
{"ie":57,"lam":{"body":56,"type":34}}
{"ie":58,"lam":{"body":57,"type":32}}
{"ie":59,"lam":{"body":58,"type":31}}
{"in":9,"str":{"pre":5,"str":"rec_1"}}
{"const":{"name":9,"us":[2]},"ie":60}
{"app":{"arg":47,"fn":60},"ie":61}
{"app":{"arg":35,"fn":61},"ie":62}
{"bvar":3,"ie":63}
{"app":{"arg":63,"fn":62},"ie":64}
{"app":{"arg":12,"fn":64},"ie":65}
{"app":{"arg":4,"fn":65},"ie":66}
{"app":{"arg":2,"fn":66},"ie":67}
{"app":{"arg":67,"fn":18},"ie":68}
{"ie":69,"lam":{"body":68,"type":29}}
{"ie":70,"lam":{"body":69,"type":46}}
{"ie":71,"lam":{"body":70,"type":40}}
{"ie":72,"lam":{"body":71,"type":34}}
{"ie":73,"lam":{"body":72,"type":32}}
{"ie":74,"lam":{"body":73,"type":31}}
{"forallE":{"body":41,"type":29},"ie":75}
{"forallE":{"body":75,"type":46},"ie":76}
{"forallE":{"body":76,"type":40},"ie":77}
{"forallE":{"body":77,"type":34},"ie":78}
{"forallE":{"body":78,"type":32},"ie":79}
{"forallE":{"body":79,"type":31},"ie":80}
{"const":{"name":8,"us":[2]},"ie":81}
{"app":{"arg":47,"fn":81},"ie":82}
{"app":{"arg":35,"fn":82},"ie":83}
{"app":{"arg":63,"fn":83},"ie":84}
{"app":{"arg":12,"fn":84},"ie":85}
{"app":{"arg":4,"fn":85},"ie":86}
{"app":{"arg":2,"fn":86},"ie":87}
{"app":{"arg":87,"fn":23},"ie":88}
{"ie":89,"lam":{"body":88,"type":28}}
{"ie":90,"lam":{"body":89,"type":46}}
{"ie":91,"lam":{"body":90,"type":40}}
{"ie":92,"lam":{"body":91,"type":34}}
{"ie":93,"lam":{"body":92,"type":32}}
{"ie":94,"lam":{"body":93,"type":31}}
{"inductive":{"ctors":[{"cidx":0,"induct":5,"isUnsafe":false,"levelParams":[],"name":6,"numFields":0,"numParams":0,"type":28},{"cidx":1,"induct":5,"isUnsafe":false,"levelParams":[],"name":7,"numFields":1,"numParams":0,"type":30}],"recs":[{"all":[5],"isUnsafe":false,"k":false,"levelParams":[3],"name":8,"numIndices":0,"numMinors":3,"numMotives":2,"numParams":0,"rules":[{"ctor":6,"nfields":0,"rhs":59},{"ctor":7,"nfields":1,"rhs":74}],"type":54},{"all":[5],"isUnsafe":false,"k":false,"levelParams":[3],"name":9,"numIndices":0,"numMinors":3,"numMotives":2,"numParams":0,"rules":[{"ctor":2,"nfields":1,"rhs":94}],"type":80}],"types":[{"all":[5],"ctors":[6,7],"isRec":true,"isReflexive":false,"isUnsafe":false,"levelParams":[],"name":5,"numIndices":0,"numNested":1,"numParams":0,"type":0}]}}
"#;

fn nested_export(num_threads: usize) -> ExportFile {
    parse_export_mapped(
        NESTED_EXPORT.as_bytes(),
        Config {
            num_threads,
            ..Config::default()
        },
    )
    .unwrap()
}

fn reject_field_count(rec_name: &str, ctor_name: &str, nfields: u16) {
    for num_threads in [1, 4] {
        let mut export = nested_export(num_threads);
        let find_name = |name: &str| {
            export
                .declars
                .keys()
                .copied()
                .find(|&n| export.display(n).to_string() == name)
                .unwrap()
        };
        let rec_name_id = find_name(rec_name);
        let ctor_name_id = find_name(ctor_name);
        let Some(Declar::Recursor(rec)) = export.declars.get_mut(&rec_name_id) else {
            panic!("expected recursor");
        };
        let rule = Arc::make_mut(&mut rec.rec_rules)
            .iter_mut()
            .find(|r| r.ctor_name == ctor_name_id)
            .unwrap();
        assert_ne!(rule.ctor_telescope_size_wo_params, nfields);
        rule.ctor_telescope_size_wo_params = nfields;
        let Err(CheckError::Rejected(error)) = export.check_all_declars() else {
            panic!("expected rejection for {rec_name}, {ctor_name}, nfields={nfields}");
        };
        assert!(
            error.0.contains(&format!(
                "recursor rule field count mismatch for {ctor_name} in {rec_name}"
            )),
            "unexpected rejection: {error}"
        );
    }
}

#[test]
fn accepts_nested_recursor_field_counts() {
    for num_threads in [1, 4] {
        nested_export(num_threads).check_all_declars().unwrap();
    }
}

#[test]
fn rejects_nested_recursor_missing_field() {
    reject_field_count("T.rec", "T.mk", 0);
}

#[test]
fn rejects_nested_recursor_extra_field() {
    reject_field_count("T.rec", "T.mk", 2);
}

#[test]
fn rejects_nested_recursor_field_on_nullary_constructor() {
    reject_field_count("T.rec", "T.base", 1);
}

#[test]
fn rejects_auxiliary_nested_recursor_missing_field() {
    reject_field_count("T.rec_1", "C.c", 0);
}

#[test]
fn rejects_auxiliary_nested_recursor_extra_field() {
    reject_field_count("T.rec_1", "C.c", 2);
}
