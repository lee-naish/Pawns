// harness for bst.pns -> bst_out.c
// or pbst.c if we use -DPure
// -DMax=n inserts n ints into the tree, unbalanced ->O(n^2)
// prints time taken
// Initial version du takes around 65% of time with -DPure
// Later version has huge difference: 2100ms vs 90ms (>20 speedup)
// Compiler is doing a very good job for du version: tight code with
// tail recursion optimised.  For pure version its hard to make it tail
// recursive due to malloc/node() so the code is recursive, using stack
// space as well as a malloc for each level traversed.
// gcc -O3 -DMax=10000 -DPure bst_main.c ; ./a.out
// gcc -O3 -DMax=10000 bst_main.c ; ./a.out
// if-then-else implemented as switch, no tail recursion opt in src,
// extra code in macros to get type checking, etc, malloc from stdlib

#ifndef Max
#define Max 0
#endif

#include <stdlib.h>
#include <stdio.h>
#include <time.h>
#include "pawns.h"
#include "bst.h"
#include "addlist.h"

// should be in some .h file??
bst  list_bst(list xs);
list  incs(list is);
list  add_lists(list xs, list ys);


void
main() {
    list l, l2, l3;
    bst t;
    clock_t t1, t2;
    intptr_t sum;

#if Max>0
    long i;
    l = nil();
    for (i = Max; i > 0; i--)
        l = cons((void*)i, l);
#else // Max
    l = cons(5L, cons(6L, cons(3L, cons(1L, cons(2L, cons(4L, cons(7L, nil())))))));
    printf("l = %lx\n", (long) l);
    print_ints(l);
#endif // Max
    t1 = clock();
    t = list_bst(l);
    t2 = clock();
    printf("list_bst took %dms\n", (int)((t2-t1)*1000/CLOCKS_PER_SEC));
#if Max==0
    l2 = incs(l); // test higher order
    print_ints(l2);
    l3 = add_lists(l,l2); // test higher order
#endif // Max
#if Max<150
    print_tree(t);
#endif // Max
    sum = bst_sum(t);
    printf("sum = %ld\n", (long)sum);
    exit(0);
}
