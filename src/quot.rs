//! Construction of quotient types

use crate::env::{ConstructorData, Declar, DeclarInfo, InductiveData, EnvLimit};
use crate::expr::BinderStyle::*;
use crate::tc::TypeChecker;
use crate::util::TcCtx;

/// From `in ctx, [a, b, c, .., n]`, create `app(app(app(a, b), c).. n)`
#[macro_export]
macro_rules! app {
    ( in $ctx:expr; $fun:expr, $arg:expr ) => {
        {
            $ctx.mk_app($fun, $arg)
        }
    };
    ( in $ctx:expr; $fun:expr, $arg:expr, $($tl:expr),*) => {
        {
            let mut base = $ctx.mk_app($fun, $arg);
            $(
                base = $ctx.mk_app(base, $tl);
            )*
            base
        }
    }
}

#[macro_export]
macro_rules! arrow {
    ( in $ctx:expr; $dom:expr, $body:expr ) => {
        {
            let anon = $ctx.anonymous();
            $ctx.mk_pi(anon, BinderStyle::Default, $dom, $body)
        }
    };
    ( in $ctx:expr; $dom:expr, $($tl:expr),* ) => {
        {
            let anon = $ctx.anonymous();
            let inner = arrow!(in $ctx; $($tl),*);
            $ctx.mk_pi(anon, BinderStyle::Default, $dom, inner)
        }
    }
}

/// The `Quot` declarations rely on `Eq` being defined as it is in
/// the prelude, so a prereq for checking the `Quot` declarations is asserting
/// that a propery constructed `Eq` and `Eq.refl`
pub fn check_eq<'x, 't: 'x, 'p: 't>(
    ctx: &'x mut TcCtx<'t, 'p>,
    cache: &mut crate::util::TcCache<'t, 't>,
    arena: &'t bumpalo::Bump,
    declar: &Declar<'t>,
) {
    use crate::expr::BinderStyle::*;
    let name = ctx.str1("Eq");
    let cname = ctx.str2("Eq", "refl");
    let alpha_name = ctx.str1("α");
    let a_name = ctx.str1("a");
    let prop = ctx.prop();
    let env = ctx.export_file.new_env(EnvLimit::ByName(declar.info().name));
    match env.get_inductive(&name).cloned() {
        // The `Eq` declaration offered up by the export file;
        Some(InductiveData { info, num_params, all_ctor_names, .. }) => {
            let eq_const = ctx.mk_const(name, info.uparams);
            assert_eq!(ctx.read_levels(info.uparams).len(), 1);
            assert_eq!(num_params, 2);
            let uparam = match ctx.read_levels(info.uparams).as_ref() {
                &[u] => ctx.mk_sort(u),
                owise => panic!("Bad `Eq` type; inductive `Eq` is expected to have 1 uparam, found {}", owise.len()),
            };
            let anon = ctx.anonymous();
            let a1 = ctx.mk_var(1);
            let inner = ctx.mk_pi(anon, Default, a1, prop);
            let a0 = ctx.mk_var(0);
            let inner = ctx.mk_pi(anon, Default, a0, inner);
            let expected = ctx.mk_pi(alpha_name, Implicit, uparam, inner);
            let mut tc = TypeChecker::new(ctx, &env, arena, Some(info), cache);
            tc.assert_def_eq(info.ty, expected);
            match all_ctor_names.as_ref() {
                &[ctor_name] => {
                    assert_eq!(cname, ctor_name);
                    match env.get_constructor(&ctor_name) {
                        Some(ConstructorData { info, .. }) => {
                            let uparam_sort = match ctx.read_levels(info.uparams).as_ref() {
                                &[uparam] => ctx.mk_sort(uparam),
                                _ => panic!(),
                            };
                            let a_alpha = ctx.mk_var(1);
                            let a_a = ctx.mk_var(0);
                            let app = app!(in ctx; eq_const, a_alpha, a_a, a_a);
                            let dom_a = ctx.mk_var(0);
                            let inner = ctx.mk_pi(a_name, Default, dom_a, app);
                            let expected = ctx.mk_pi(alpha_name, Implicit, uparam_sort, inner);
                            let mut tc = TypeChecker::new(ctx, &env, arena, Some(*info), cache);
                            tc.assert_def_eq(info.ty, expected);
                        }
                        None => panic!(
                            "cannot add Quot; constructor `Eq.refl` was expected, but not found in the environment"
                        ),
                    }
                }
                owise => panic!(
                    "cannot add Quot; `Eq` type improperly formed; expected one constructor, found {}",
                    owise.len()
                ),
            }
        }
        None => panic!("cannot add Quot; improperly formed `Eq` type := {:?} ", ctx.debug_print(declar.info().name)),
    }
}

#[allow(non_snake_case)]
pub fn check_quot<'x, 't: 'x, 'p: 't>(
    ctx: &'x mut TcCtx<'t, 'p>,
    cache: &mut crate::util::TcCache<'t, 't>,
    arena: &'t bumpalo::Bump,
    declar: &Declar<'t>,
) {
    // `Eq` matching expectations is a prerequisite for checking `Quot`.
    let prop = ctx.prop();
    let u_name = ctx.str1("u");
    let v_name = ctx.str1("v");
    let q_name = ctx.str1("q");
    let u_level = ctx.param(u_name);
    let v_level = ctx.param(v_name);
    let sort_u = ctx.mk_sort(u_level);
    let sort_v = ctx.mk_sort(v_level);

    let levels_u = ctx.alloc_levels_slice(&[u_level]);
    let levels_v = ctx.alloc_levels_slice(&[v_level]);
    let levels_uv = ctx.alloc_levels_slice(&[u_level, v_level]);
    let quot_name = ctx.export_file.name_cache.quot.unwrap();
    let quot_mk_name = ctx.export_file.name_cache.quot_mk.unwrap();

    let A_name = ctx.str1("A");
    let B_name = ctx.str1("B");
    let r_name = ctx.str1("r");
    let f_name = ctx.str1("f");
    let a_name = ctx.str1("a");
    let b_name = ctx.str1("b");
    let anon = ctx.anonymous();


    let r_dom = {
        let a1 = ctx.mk_var(1);
        let inner = ctx.mk_pi(anon, Default, a1, prop);
        let a0 = ctx.mk_var(0);
        ctx.mk_pi(anon, Default, a0, inner)
    };

    let expected_quot = Declar::Quot {
        info: DeclarInfo {
            name: quot_name,
            uparams: levels_u,
            ty: {
                let inner = ctx.mk_pi(r_name, Default, r_dom, sort_u);
                ctx.mk_pi(A_name, Implicit, sort_u, inner)
            },
        },
    };
    let quot_const = ctx.mk_const(expected_quot.info().name, levels_u);

    // Quot.mk : Π {A : Sort u} (r : A → A → Prop), A → @Quot A r
    let expected_quot_mk = Declar::Quot {
        info: DeclarInfo {
            name: quot_mk_name,
            uparams: levels_u,
            ty: {
                let a2 = ctx.mk_var(2);
                let a1 = ctx.mk_var(1);
                let quot_app = app!(in ctx; quot_const, a2, a1);
                let dom = ctx.mk_var(1);
                let arr = ctx.mk_pi(anon, Default, dom, quot_app);
                let inner = ctx.mk_pi(r_name, Default, r_dom, arr);
                ctx.mk_pi(A_name, Implicit, sort_u, inner)
            },
        },
    };

    let quot_mk_const = ctx.mk_const(expected_quot_mk.info().name, levels_u);
    let eq_name = ctx.str1("Eq");
    let eq_const = ctx.mk_const(eq_name, levels_v);

    if declar.info().name == ctx.str1("Quot") {
        let env = ctx.export_file.new_env(EnvLimit::ByName(quot_name));
        let mut tc = TypeChecker::new(ctx, &env, arena, Some(*declar.info()), cache);
        tc.assert_def_eq(declar.info().ty, expected_quot.info().ty);
    } else if declar.info().name == ctx.str2("Quot", "mk") {
        let env = ctx.export_file.new_env(EnvLimit::ByName(quot_mk_name));
        let mut tc = TypeChecker::new(ctx, &env, arena, Some(*declar.info()), cache);
        tc.assert_def_eq(declar.info().ty, expected_quot_mk.info().ty);
    } else if declar.info().name == ctx.str2("Quot", "lift") {
        check_eq(ctx, cache, arena, declar);
        // Quot.lift : Π {A : Sort u} {r : A → A → Prop} {B : Sort v} (f : A → B),
        //   (∀ (a b : A), r a b → f a = f b) → @Quot A r → B
        let expected_quot_lift = Declar::Quot {
            info: DeclarInfo {
                name: declar.info().name,
                uparams: levels_uv,
                ty: {
                    let f_dom = {
                        let a = ctx.mk_var(2);
                        let b = ctx.mk_var(1);
                        ctx.mk_pi(anon, Default, a, b)
                    };
                    let lift_inner = {
                        let r_at = ctx.mk_var(4);
                        let a_at = ctx.mk_var(1);
                        let b_at = ctx.mk_var(0);
                        let rab = app!(in ctx; r_at, a_at, b_at);
                        let b_ty = ctx.mk_var(4);
                        let f_at = ctx.mk_var(3);
                        let a_at2 = ctx.mk_var(2);
                        let b_at2 = ctx.mk_var(1);
                        let fa = ctx.mk_app(f_at, a_at2);
                        let fb = ctx.mk_app(f_at, b_at2);
                        let eq_app = app!(in ctx; eq_const, b_ty, fa, fb);
                        let arr = ctx.mk_pi(anon, Default, rab, eq_app);
                        let b_dom = ctx.mk_var(4);
                        let inner_b = ctx.mk_pi(b_name, Default, b_dom, arr);
                        let a_dom = ctx.mk_var(3);
                        ctx.mk_pi(a_name, Default, a_dom, inner_b)
                    };
                    let quot_at = {
                        let a = ctx.mk_var(4);
                        let r_at = ctx.mk_var(3);
                        app!(in ctx; quot_const, a, r_at)
                    };
                    let body = ctx.mk_var(3);
                    let arr2 = ctx.mk_pi(anon, Default, quot_at, body);
                    let arr1 = ctx.mk_pi(anon, Default, lift_inner, arr2);
                    let f_pi = ctx.mk_pi(f_name, Default, f_dom, arr1);
                    let b_pi = ctx.mk_pi(B_name, Implicit, sort_v, f_pi);
                    let r_pi = ctx.mk_pi(r_name, Default, r_dom, b_pi);
                    ctx.mk_pi(A_name, Implicit, sort_u, r_pi)
                },
            },
        };
        let env = ctx.export_file.new_env(EnvLimit::ByName(declar.info().name));
        let mut tc = TypeChecker::new(ctx, &env, arena, Some(*declar.info()), cache);
        tc.assert_def_eq(declar.info().ty, expected_quot_lift.info().ty);
        return
    } else if declar.info().name == ctx.str2("Quot", "ind") {
        //           (∀ (a : A), B (@Quot.mk A r a)) → ∀ (q : @Quot A r), B q
        let expected_quot_ind = Declar::Quot {
            info: DeclarInfo {
                name: declar.info().name,
                uparams: levels_u,
                ty: {
                    let b_dom = {
                        let a = ctx.mk_var(1);
                        let r_at = ctx.mk_var(0);
                        let q = app!(in ctx; quot_const, a, r_at);
                        ctx.mk_pi(anon, Default, q, prop)
                    };
                    let lhs = {
                        let a_dom = ctx.mk_var(2);
                        let b_at = ctx.mk_var(1);
                        let a_at = ctx.mk_var(3);
                        let r_at = ctx.mk_var(2);
                        let a_var = ctx.mk_var(0);
                        let mk_app = app!(in ctx; quot_mk_const, a_at, r_at, a_var);
                        let body = ctx.mk_app(b_at, mk_app);
                        ctx.mk_pi(a_name, Default, a_dom, body)
                    };
                    let rhs = {
                        let a_at = ctx.mk_var(3);
                        let r_at = ctx.mk_var(2);
                        let q_dom = app!(in ctx; quot_const, a_at, r_at);
                        let b_at = ctx.mk_var(2);
                        let q_var = ctx.mk_var(0);
                        let body = ctx.mk_app(b_at, q_var);
                        ctx.mk_pi(q_name, Default, q_dom, body)
                    };
                    let arr = ctx.mk_pi(anon, Default, lhs, rhs);
                    let b_pi = ctx.mk_pi(B_name, Implicit, b_dom, arr);
                    let r_pi = ctx.mk_pi(r_name, Default, r_dom, b_pi);
                    ctx.mk_pi(A_name, Implicit, sort_u, r_pi)
                },
            },
        };

        let env = ctx.export_file.new_env(EnvLimit::ByName(declar.info().name));
        let mut tc = TypeChecker::new(ctx, &env, arena, Some(*declar.info()), cache);
        tc.assert_def_eq(declar.info().ty, expected_quot_ind.info().ty);
        return
    } else {
        panic!("invalid quotient declaration {:?}", ctx.debug_print(declar.info().name))
    }
}
