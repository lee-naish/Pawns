// harness for wam.pns -> wam_out.c

#include <stdlib.h>
#include <stdio.h>
#include "wam_adt.h"
#include "wam_out.c"


bool
eq(fs i, fs j) {
    if (((intptr_t)i & 7) == ((intptr_t)j & 7)) % XXXX
        return true();
    else
        return false();
}

__inline bool
eq_ptr(term* i, term* j) {
    if (i == j)
        return true();
    else
        return false();
}

void
print_var(term *i) {
    printf("_%lx ", (intptr_t)i);
}

void
print_fs(fs i) {
    printf("f%ld ", (intptr_t)i & 7); % XXXX
}

void
main() {
    bool b;
    term t, t1, t2, t3, t4, t5;
    t = nv(f0(), nil());
    t2 = newvar();
    t1 = nv(f2(), cons(t, cons(t2, nil())));
    print_term(&t1);
    printf("\n");
    t4 = var(var(newvar()));
    t3 = nv(f2(), cons(t4, cons(t4, nil())));
    print_term(&t3);
    printf("\n");
    b = unify(&t1, &t3);
    // printf("true %lx\n", (intptr_t)true() & 7);
    // printf("false %lx\n", (intptr_t)false() & 7);
    // printf("b %lx\n", (intptr_t)b & 7);
    if(((intptr_t)b & 7) == ((intptr_t)true() & 7))
        printf("succeeded\n");
    else
        printf("failed\n");
    print_term(&t3);
    printf("\n");
    print_term(&t2);
    printf("\n");
}
