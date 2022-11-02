/*
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
*/

#include <lean/lean.h>
#include <string.h>
#include <stdlib.h>
#include <ccadical.h>

/*
CaDiCaL C API shim to Lean
*/

// Declare external class

static lean_external_class* leancadical_external_class = NULL;

static inline void leancadical_finalizer(void *ptr)
{
    CCaDiCaL *solver = (CCaDiCaL *) ptr;
    ccadical_release(solver);
    free(solver);
}

static inline void leancadical_foreach(void *mod, b_lean_obj_arg fn) {
}

lean_obj_res leancadical_initialize()
{
    leancadical_external_class = lean_register_external_class(leancadical_finalizer, leancadical_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}



// Getting into/out of lean_obj*

lean_obj_res leancadical_box(CCaDiCaL *solver) {
    return lean_alloc_external(leancadical_external_class, solver);
}

CCaDiCaL *leancadical_unbox(lean_obj_arg o) {
    return (CCaDiCaL*) (lean_get_external_data(o));
}

// Exclusivity checking

static inline void leancadical_ensure_exclusive(lean_obj_arg a) {
    if (LEAN_LIKELY(lean_is_exclusive(a)))
        return;
    
    if (lean_is_persistent(a)) {
        lean_panic_fn(NULL, lean_mk_string(
            "Lean CaDiCaL API: Solver object marked persistent. (Try `set_option compiler.extract_closed false`)"
        ));
    } else {
        lean_panic_fn(NULL, lean_mk_string(
            "Lean CaDiCaL API: Solver object not exclusive."
        ));
    }
}


// Making a new solver

lean_obj_res leancadical_new() {
    CCaDiCaL *solver = ccadical_init();
    return leancadical_box(solver);
}

// Adding a clause to the solver

lean_obj_res leancadical_add_clause(lean_obj_arg s, b_lean_obj_arg L) {
    leancadical_ensure_exclusive(s);
    CCaDiCaL *solver = leancadical_unbox(s);

    b_lean_obj_arg L_ = L;

    // While not nil,
    while (L_ != lean_box(0)) {
        // get the head
        b_lean_obj_arg x = lean_ctor_get(L_, 0);

        // unpack
        assert(lean_is_scalar(x));
        assert(lean_unbox(x) <= INT_MAX);

        // add literal to clause
        ccadical_add(solver, (int)lean_unbox(x));

        // move on to the tail
        L_ = lean_ctor_get(L_, 1);
    }

    ccadical_add(solver, 0);

    return s;
}

// Asking solver to solve

lean_obj_res leancadical_solve(lean_obj_arg s) {
    leancadical_ensure_exclusive(s);
    CCaDiCaL *solver = leancadical_unbox(s);

    int r = ccadical_solve(solver);

    // return tuple (s,r)
    lean_obj_res res = lean_alloc_ctor(0,2,0);
    lean_ctor_set(res, 0, s);

    if (r == 10) {
        lean_obj_res res1 = lean_alloc_ctor(1,1,0);
        lean_ctor_set(res1, 0, lean_box(1));
        lean_ctor_set(res, 1, res1);
    } else if (r == 20) {
        lean_obj_res res1 = lean_alloc_ctor(1,1,0);
        lean_ctor_set(res1, 0, lean_box(0));
        lean_ctor_set(res, 1, res1);
    } else {
        lean_ctor_set(res, 1, lean_box(0));
    }

    return res;
}

// Getting values from solver
// (note: assumes solver is in SAT state)

lean_obj_res leancadical_value (b_lean_obj_arg s, b_lean_obj_arg n) {
    CCaDiCaL *solver = leancadical_unbox(s);

    //assert(ccadical_status(solver) == 10);

    assert(lean_is_scalar(n));
    int l = lean_unbox(n);

    assert(0 < l && l <= INT_MAX);

    int r = ccadical_val(solver, (int)lean_unbox(n));

    lean_obj_res res;
    
    if (r == l) {
        res = lean_alloc_ctor(1,1,0);
        lean_ctor_set(res, 0, lean_box(1));
    } else if (r == -l) {
        res = lean_alloc_ctor(1,1,0);
        lean_ctor_set(res, 0, lean_box(0));
    } else {
        res = lean_box(0);
    }

    return res;
}
