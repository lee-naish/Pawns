#ifndef PAWNS_H
#define PAWNS_H
// GC stuff - gcc flags don't seem to work
// adtpp allows us to override default malloc/free
#define ADT_MALLOC(s) GC_MALLOC(s)
#define ADT_FREE(s) GC_FREE(s)
// #define ADT_MALLOC(s) malloc(s)
// #define ADT_FREE(s) free(s)
// XXX fix include path
#include <gc.h>
// #include "/home/lee/lib/gc/include/gc/gc.h"
// #include "~/lib/gc/include/gc/gc.h"

// header file for compiled Pawns code
// defines a couple of types used in foo.h, generated from foo.adt by
// adtpp plus prototypes and definitions of some simple builtins.  We
// could get the Pawns compiler to inline some of this but we get gcc to
// do it instead. The functions are static so they can be defined in
// several files which are linked.
// XXX need to add a bunch more (see also comp.pl)
// bool is munged by prefixing with PAWNS_ - maybe do the same for int

#include <stdint.h> // need intptr_t etc
#include <stdio.h>  // need printf prototype etc

typedef int *********************_void_ptr;
typedef void (*_func_ptr)(void*);

#include "builtin.h" // XXX rename

// XXX use macros rather than inline function for some of these, like plus
// and minus

static intptr_t plus(intptr_t, intptr_t);
static intptr_t minus(intptr_t, intptr_t);
static PAWNS_bool leq(intptr_t, intptr_t);
static intptr_t eq(intptr_t, intptr_t);
static void print_int(intptr_t);

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

static __inline void
print_int(intptr_t i) {
    // printf("%ld ", (long)i);
    printf("%ld\n", (long)i);
}

#endif // PAWNS_H
