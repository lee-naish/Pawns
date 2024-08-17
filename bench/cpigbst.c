// hacked version of bst.c from bst.pns with iterative inner loop
// - a few versions
// - also can experiment with malloc vs GC_malloc

#define version 3

// prettier version of data type for version 3
typedef struct tree_node *tree;
struct tree_node {
    tree *left;
    long data;
    tree *right;};

#include "pawns.h"
#include "bst.h"
void  main();
bst  list_bst(list xs);
bst  bst_insert(intptr_t x, bst t0);
void  bst_insert1(intptr_t x, bst t0, bst *r);
static __inline void  bstmain();
static __inline intptr_t  bst_size(bst t);
static __inline list  ones(intptr_t n);
static __inline list  ones_acc(intptr_t n, list xs);
static __inline void  print_tree(bst t);
static __inline void  print_int(intptr_t i);


void 
main() {
    bstmain();
    return;
}

bst 
list_bst(list xs) {
    bst t = mt();
    while(1)
        if_cons(xs, x, xs1)
            t = bst_insert(x, t);
            xs = xs1;
        else()
            break;
        end_if()
    return t;
}

// iterative version - we pass in a pointer to tree to clobber
bst
bst_insert(intptr_t x, bst t0) {
    bst rt;
    bst_insert1(x, t0, &rt);
    return rt;
}

void
bst_insert1(intptr_t x, bst t0, bst *rt) {
  while (1) {
    switch_bst(t0)
    case_mt_ptr()
        bst V1 = mt();
        bst V2 = mt();
        bst V0 = node(V1, x, V2);
        *rt = V0;
        return;
    case_node_ptr(V3, V4, V5)
        bst r = *V5;
        intptr_t n = *V4;
        bst l = *V3;
        if (x <= n) {
            bst V8;
            bst V7 = node(V8, n, r);
            ADT_FREE(t0);
// printf("%lx %lx %lx %lx\n", (long)t0, (long)l, (long)rt, (long)V7);
            t0 = l;
            *rt = V7;
            rt = &((struct _ADT_bst_node*)V7)->f0;
        } else {
            bst V10;
            bst V9 = node(l, n, V10);
            ADT_FREE(t0);
            t0 = r;
            *rt = V9;
            rt = &((struct _ADT_bst_node*)V9)->f2;
        }
    end_switch()
  }
}


static __inline intptr_t 
bst_size(bst t) {
    switch_bst(t)
    case_mt_ptr()
        intptr_t V0 = 0;
        return(V0);
    case_node_ptr(V1, V2, V3)
        bst r = *V3;
        intptr_t n = *V2;
        bst l = *V1;
        intptr_t V6 = 1;
        intptr_t V7 = bst_size(l);
        intptr_t V5 = plus(V6, V7);
        intptr_t V8 = bst_size(r);
        intptr_t V4 = plus(V5, V8);
        return(V4);
    end_switch()
}

static __inline list 
ones(intptr_t n) {
    list V1 = nil();
    list V0 = ones_acc(n, V1);
    return(V0);
}

static __inline list 
ones_acc(intptr_t n, list xs) {
    intptr_t V1 = 0;
    PAWNS_bool V0 = leq(n, V1);
    switch_PAWNS_bool(V0)
    case_PAWNS_true_ptr()
        return(xs);
    case_PAWNS_false_ptr()
        intptr_t V4 = 1;
        intptr_t V3 = minus(n, V4);
        intptr_t V6 = 1;
        list V5 = cons(V6, xs);
        list V2 = ones_acc(V3, V5);
        return(V2);
    end_switch()
}


#ifdef DEBUG
static __inline void
bstmain() {
    intptr_t V1 = 5;
    list V0 = ones(V1);
    bst t = list_bst(V0);
    print_tree(t);
    intptr_t V4 = bst_size(t);
    print_int(V4);
    return;
}
#else // DEBUG
static __inline void 
bstmain() {
    intptr_t V4 = 30000;
    list V3 = ones(V4);
    bst V2 = list_bst(V3);
    intptr_t V1 = bst_size(V2);
    print_int(V1);
    return;
}
#endif // DEBUG


static __inline void
print_tree(bst t) {
    printf("(");
    switch_bst(t)
    case_mt_ptr()
        printf(")");
        return;
    case_node_ptr(V1, V2, V3)
        bst r = *V3;
        intptr_t n = *V2;
        bst l = *V1;
        print_tree(l);
        print_int(n);
        print_tree(r);
        printf(")");
        return;
    end_switch()
}

static __inline void
print_int(intptr_t i){
printf("%ld\n", (long)i);
}

