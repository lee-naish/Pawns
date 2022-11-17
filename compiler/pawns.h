#ifndef PAWNS_H
#define PAWNS_H
// Header file for compiled Pawns code.
// Defines some builtin types and functions.
// The type stuff is generated by adtpp but we need to prefix
// it and postfix it with other stuff so we have two files.
// XXX They should be installed somewhere and included with
// <pawns.h> instead of "pawns.h".
// We could get the Pawns compiler to inline some of this but we get gcc to
// do it instead. The functions are static so they can be defined in
// several files which are linked.
// Could separate some stuff and put in in a library instead
// XXX need to add a bunch more (see also comp.pl)
// bool is munged by prefixing with PAWNS_ - maybe do the same for int
// XXX probably should migrate compiled version of
// ../examples/array.pns here also

// GC stuff - gcc flags don't seem to work
// adtpp allows us to override default malloc/free
#define ADT_MALLOC(s) GC_MALLOC(s)
#define ADT_FREE(s) GC_FREE(s)
// Last time I looked,
// by default the Boehm et al garbage collector .h file has
// #define GC_MALLOC(s) GC_malloc(s)
// #define GC_FREE(s) GC_free(s)
// and prototypes for these functions.  This should be
// sufficient if gc.h isn't installed properly or you want to
// avoid reading it.
#include <gc.h>

#include <stdint.h> // need intptr_t etc

// needed printf prototype etc for print_int builtin
// probably best to have all io stuff elsewhere
// #include <stdio.h>

typedef int *********************_void_ptr;
typedef void (*_func_ptr)(void*);

#include "builtin.h" // XXX rename?

// XXX use macros rather than inline function for some of these, like plus
// and minus

static intptr_t plus(intptr_t, intptr_t);
static intptr_t minus(intptr_t, intptr_t);
static PAWNS_bool leq(intptr_t, intptr_t);
static intptr_t eq(intptr_t, intptr_t);
// static void print_int(intptr_t);

static __inline PAWNS_bool
leq(intptr_t i, intptr_t j) {
    if(i <= j)
        return PAWNS_true();
    else
        return PAWNS_false();
}

static __inline intptr_t
plus(intptr_t i, intptr_t j) {
    return i+j;
}

static __inline intptr_t
minus(intptr_t i, intptr_t j) {
    return i-j;
}

// static __inline void
// print_int(intptr_t i) {
//     // printf("%ld ", (long)i);
//     printf("%ld\n", (long)i);
// }

static __inline void *
apply(_closure cl, void *a1) {
    _func_ptr r;
    void *ca1, *ca2, *ca3, *ca4;
    intptr_t aty;

    switch__closure(cl)
    case__cl0(f, aty)
        if (aty==1)
             return (*(void*(*)(void*))f)(a1);
        else
             return (void *) _cl1(f, aty, a1);
    case__cl1(f, aty, ca1)
        if (aty==2)
            return (*(void*(*)(void*,void*))f)(ca1, a1);
        else
            return (void *) _cl2(f, aty, ca1, a1);
    case__cl2(f, aty, ca1, ca2)
        if (aty==3)
            return (*(void*(*)(void*,void*,void*))f)(ca1, ca2, a1);
        else
            return (void *) _cl3(f, aty, ca1, ca2, a1);
    case__cl3(f, aty, ca1, ca2, ca3)
        if (aty==4)
            return (*(void*(*)(void*,void*,void*,void*))f)(ca1, ca2, ca3, a1);
        else
            return (void *) _cl4(f, aty, ca1, ca2, ca3, a1);
    case__cl4(f, aty, ca1, ca2, ca3, ca4)
        return (*(void*(*)(void*,void*,void*,void*,void*))f)(ca1, ca2, ca3, ca4, a1);
    end_switch()
}

#endif // PAWNS_H
