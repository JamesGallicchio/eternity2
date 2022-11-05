/*
Copyright (c) 2022 James Gallicchio.

Authors: James Gallicchio
*/

#include <lean/lean.h>
#include <string.h>
#include <stdlib.h>
#include <kissat.h>
#include <stdio.h>

/*
Kissat C API shim to Lean
*/

// Declare external class

static lean_external_class* leankissat_external_class = NULL;

static inline void leankissat_finalizer(void *ptr)
{
    kissat *solver = (kissat *) ptr;
    kissat_release(solver);
}

static inline void leankissat_foreach(void *mod, b_lean_obj_arg fn) {
}

lean_obj_res leankissat_initialize()
{
    leankissat_external_class = lean_register_external_class(leankissat_finalizer, leankissat_foreach);
    return lean_io_result_mk_ok(lean_box(0));
}



// Getting into/out of lean_obj*

static inline lean_obj_res leankissat_box(kissat *solver) {
    return lean_alloc_external(leankissat_external_class, solver);
}

static inline kissat *leankissat_unbox(lean_obj_arg o) {
    return (kissat*) (lean_get_external_data(o));
}

// Exclusivity checking

static inline void leankissat_ensure_exclusive(lean_obj_arg a) {
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

lean_obj_res leankissat_new(b_lean_obj_arg unit) {
    assert (unit == lean_box(0));

    kissat *solver = kissat_init();
    kissat_set_option(solver, "quiet", 1);
    return leankissat_box(solver);
}

// Adding a clause to the solver

lean_obj_res leankissat_add_clause(lean_obj_arg s, b_lean_obj_arg L) {
    leankissat_ensure_exclusive(s);
    kissat *solver = leankissat_unbox(s);

    b_lean_obj_arg L_ = L;

    // While not nil,
    while (L_ != lean_box(0)) {
        // get the head
        b_lean_obj_res x = lean_ctor_get(L_, 0);

        assert(lean_is_ctor(x));
        assert(lean_ctor_num_objs(x) == 2);
        
        b_lean_obj_res neg = lean_ctor_get(x, 0);
        b_lean_obj_res num = lean_ctor_get(x, 1);

        assert(lean_is_scalar(neg));
        assert(lean_unbox(neg) < 2);
        bool isNeg = lean_unbox(neg);

        assert(lean_is_scalar(num));
        assert(0 < lean_unbox(num));
        assert(lean_unbox(num) < INT_MAX);
        size_t var = lean_unbox(num);

        int signedVar = (isNeg ? -((int)var) : (int)var);

        // add literal to clause
        kissat_add(solver, signedVar);

        // move on to the tail
        L_ = lean_ctor_get(L_, 1);
    }

    kissat_add(solver, 0);

    return s;
}

// Asking solver to solve

lean_obj_res leankissat_solve(lean_obj_arg s) {
    leankissat_ensure_exclusive(s);
    kissat *solver = leankissat_unbox(s);

    int r = kissat_solve(solver);

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

lean_obj_res leankissat_value (b_lean_obj_arg s, b_lean_obj_arg n) {
    kissat *solver = leankissat_unbox(s);

    //assert(kissat_status(solver) == 10);

    assert(lean_is_scalar(n));
    int l = lean_unbox(n);

    assert(0 < l);
    assert(l < INT_MAX);

    int r = kissat_value(solver, (int)l);

    lean_obj_res res;
    
    if (r == l) {
        res = lean_alloc_ctor(1,1,0);
        lean_ctor_set(res, 0, lean_box(1));
        lean_inc(res);
    } else if (r == -l) {
        res = lean_alloc_ctor(1,1,0);
        lean_ctor_set(res, 0, lean_box(0));
        lean_inc(res);
    } else {
        res = lean_box(0);
    }

    return res;
}
