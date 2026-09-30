// SPDX-FileCopyrightText: 2026 Jeremy Chen
// SPDX-License-Identifier: Apache-2.0

//! Construction of quotient types

use crate::checker::context::TcCtx;
use crate::checker::env::{ConstructorData, Declar, DeclarInfo, EnvLimit, InductiveData};
use crate::checker::tc::TypeChecker;
use crate::outcome::{ensure_eq, reject};

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
            $ctx.mk_pi($dom, $body)
        }
    };
    ( in $ctx:expr; $dom:expr, $($tl:expr),* ) => {
        {
            let inner = arrow!(in $ctx; $($tl),*);
            $ctx.mk_pi($dom, inner)
        }
    }
}

/// The `Quot` declarations rely on `Eq` being defined as it is in
/// the prelude, so a prereq for checking the `Quot` declarations is asserting
/// that a propery constructed `Eq` and `Eq.refl`
pub fn check_eq<'x, 't: 'x, 'p: 't>(
    ctx: &'x mut TcCtx<'t, 'p>,
    cache: &mut crate::checker::cache::TcCache<'t, 't>,
    arena: &'t bumpalo::Bump,
    declar: &Declar<'t>,
) {
    let name = ctx.str1("Eq");
    let cname = ctx.str2("Eq", "refl");

    let prop = ctx.prop();
    let env = ctx
        .export_file
        .new_env(EnvLimit::ByName(declar.info().name));
    // The `Eq` declaration offered up by the export file;
    let Some(InductiveData {
        info,
        num_params,
        all_ctor_names,
        ..
    }) = env.get_inductive(name).cloned()
    else {
        reject!(
            "cannot add Quot; improperly formed `Eq` type := {:?} ",
            ctx.debug_print(declar.info().name)
        )
    };
    let eq_const = ctx.mk_const(name, info.uparams);
    ensure_eq!(info.uparams.as_ref().len(), 1);
    ensure_eq!(num_params, 2);
    let &[u] = info.uparams.as_ref() else {
        reject!(
            "Bad `Eq` type; inductive `Eq` is expected to have 1 uparam, found {}",
            info.uparams.as_ref().len()
        )
    };
    let uparam = ctx.mk_sort(u);

    let a1 = ctx.mk_var(1);
    let inner = ctx.mk_pi(a1, prop);
    let a0 = ctx.mk_var(0);
    let inner = ctx.mk_pi(a0, inner);
    let expected = ctx.mk_pi(uparam, inner);
    let mut tc = TypeChecker::new(ctx, &env, arena, Some(info), cache);
    tc.assert_def_eq(info.ty, expected);
    let &[ctor_name] = all_ctor_names.as_ref() else {
        reject!(
            "cannot add Quot; `Eq` type improperly formed; expected one constructor, found {}",
            all_ctor_names.len()
        )
    };
    ensure_eq!(cname, ctor_name);
    let Some(ConstructorData { info, .. }) = env.get_constructor(ctor_name) else {
        reject!(
            "cannot add Quot; constructor `Eq.refl` was expected, but not found in the environment"
        )
    };
    let &[uparam] = info.uparams.as_ref() else {
        reject!("`Eq.refl` must have exactly one universe parameter")
    };
    let uparam_sort = ctx.mk_sort(uparam);
    let a_alpha = ctx.mk_var(1);
    let a_a = ctx.mk_var(0);
    let app = app!(in ctx; eq_const, a_alpha, a_a, a_a);
    let dom_a = ctx.mk_var(0);
    let inner = ctx.mk_pi(dom_a, app);
    let expected = ctx.mk_pi(uparam_sort, inner);
    let mut tc = TypeChecker::new(ctx, &env, arena, Some(*info), cache);
    tc.assert_def_eq(info.ty, expected);
}

#[allow(non_snake_case)]
pub fn check_quot<'x, 't: 'x, 'p: 't>(
    ctx: &'x mut TcCtx<'t, 'p>,
    cache: &mut crate::checker::cache::TcCache<'t, 't>,
    arena: &'t bumpalo::Bump,
    declar: &Declar<'t>,
) {
    // `Eq` matching expectations is a prerequisite for checking `Quot`.
    let prop = ctx.prop();
    let u_name = ctx.str1("u");
    let v_name = ctx.str1("v");

    let u_level = ctx.param(u_name);
    let v_level = ctx.param(v_name);
    let sort_u = ctx.mk_sort(u_level);
    let sort_v = ctx.mk_sort(v_level);

    let levels_u = ctx.alloc_levels_slice(&[u_level]);
    let levels_v = ctx.alloc_levels_slice(&[v_level]);
    let levels_uv = ctx.alloc_levels_slice(&[u_level, v_level]);
    let quot_name = ctx.export_file.name_cache.quot.unwrap();
    let quot_mk_name = ctx.export_file.name_cache.quot_mk.unwrap();

    let r_dom = {
        let a1 = ctx.mk_var(1);
        let inner = ctx.mk_pi(a1, prop);
        let a0 = ctx.mk_var(0);
        ctx.mk_pi(a0, inner)
    };

    let expected_quot = Declar::Quot {
        info: DeclarInfo {
            name: quot_name,
            uparams: levels_u,
            ty: {
                let inner = ctx.mk_pi(r_dom, sort_u);
                ctx.mk_pi(sort_u, inner)
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
                let arr = ctx.mk_pi(dom, quot_app);
                let inner = ctx.mk_pi(r_dom, arr);
                ctx.mk_pi(sort_u, inner)
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
                        ctx.mk_pi(a, b)
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
                        let arr = ctx.mk_pi(rab, eq_app);
                        let b_dom = ctx.mk_var(4);
                        let inner_b = ctx.mk_pi(b_dom, arr);
                        let a_dom = ctx.mk_var(3);
                        ctx.mk_pi(a_dom, inner_b)
                    };
                    let quot_at = {
                        let a = ctx.mk_var(4);
                        let r_at = ctx.mk_var(3);
                        app!(in ctx; quot_const, a, r_at)
                    };
                    let body = ctx.mk_var(3);
                    let arr2 = ctx.mk_pi(quot_at, body);
                    let arr1 = ctx.mk_pi(lift_inner, arr2);
                    let f_pi = ctx.mk_pi(f_dom, arr1);
                    let b_pi = ctx.mk_pi(sort_v, f_pi);
                    let r_pi = ctx.mk_pi(r_dom, b_pi);
                    ctx.mk_pi(sort_u, r_pi)
                },
            },
        };
        let env = ctx
            .export_file
            .new_env(EnvLimit::ByName(declar.info().name));
        let mut tc = TypeChecker::new(ctx, &env, arena, Some(*declar.info()), cache);
        tc.assert_def_eq(declar.info().ty, expected_quot_lift.info().ty);
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
                        ctx.mk_pi(q, prop)
                    };
                    let lhs = {
                        let a_dom = ctx.mk_var(2);
                        let b_at = ctx.mk_var(1);
                        let a_at = ctx.mk_var(3);
                        let r_at = ctx.mk_var(2);
                        let a_var = ctx.mk_var(0);
                        let mk_app = app!(in ctx; quot_mk_const, a_at, r_at, a_var);
                        let body = ctx.mk_app(b_at, mk_app);
                        ctx.mk_pi(a_dom, body)
                    };
                    let rhs = {
                        let a_at = ctx.mk_var(3);
                        let r_at = ctx.mk_var(2);
                        let q_dom = app!(in ctx; quot_const, a_at, r_at);
                        let b_at = ctx.mk_var(2);
                        let q_var = ctx.mk_var(0);
                        let body = ctx.mk_app(b_at, q_var);
                        ctx.mk_pi(q_dom, body)
                    };
                    let arr = ctx.mk_pi(lhs, rhs);
                    let b_pi = ctx.mk_pi(b_dom, arr);
                    let r_pi = ctx.mk_pi(r_dom, b_pi);
                    ctx.mk_pi(sort_u, r_pi)
                },
            },
        };

        let env = ctx
            .export_file
            .new_env(EnvLimit::ByName(declar.info().name));
        let mut tc = TypeChecker::new(ctx, &env, arena, Some(*declar.info()), cache);
        tc.assert_def_eq(declar.info().ty, expected_quot_ind.info().ty);
    } else {
        reject!(
            "invalid quotient declaration {:?}",
            ctx.debug_print(declar.info().name)
        )
    }
}
