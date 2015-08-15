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
void  list_bst_du(list xs, bst* tp);
#if version==3
void  bst_insert_du(long x, tree *tp);
#else
void  bst_insert_du(intptr_t x, bst* tp);
#endif
static __inline void  bstmain();
static __inline intptr_t  bst_size(bst t);
static __inline list  ones(intptr_t n);
static __inline list  ones_acc(intptr_t n, list xs);
static __inline void  print_tree(bst t);


void 
main() {
    bstmain();
    return;
}

bst 
list_bst(list xs) {
    bst V0 = mt();
    bst* tp = (bst*)ADT_MALLOC(sizeof(void*));
    *tp=V0;
    list_bst_du(xs, tp);
    bst V2 = *tp;
    return(V2);
}

void 
list_bst_du(list xs, bst* tp) {
    switch_list(xs)
    case_cons_ptr(V0, V1)
        list xs1 = *V1;
        intptr_t x = *V0;
        bst_insert_du(x, tp);
        list_bst_du(xs1, tp);
        return;
    case_nil_ptr()
        return;
    end_switch()
}


// version 0 produced by Pawns compiler
#if version==0
void 
bst_insert_du(intptr_t x, bst* tp) {
    bst V0 = *tp;
    switch_bst(V0)
    case_mt_ptr()
        bst V2 = mt();
        bst V3 = mt();
        bst V1 = node(V2, x, V3);
        *tp=V1;
    case_node_ptr(lp, V4, rp)
        intptr_t n = *V4;
        PAWNS_bool V5 = leq(x, n);
        switch_PAWNS_bool(V5)
        case_PAWNS_true_ptr()
            bst_insert_du(x, lp);
            return;
        case_PAWNS_false_ptr()
            bst_insert_du(x, rp);
            return;
        end_switch()
    end_switch()
}
#endif // version

#if version==1
void 
bst_insert_du(intptr_t x, bst* tp) {
    bst V0 = *tp;
    while(1) {
    if_node_ptr(*tp, lp, V4, rp)
        intptr_t n = *V4;
	if (x <= n)
            tp = lp;
        else
            tp = rp;
    else()
        bst V2 = mt();
        bst V3 = mt();
        bst V1 = node(V2, x, V3);
        *tp=V1;
	return;
    end_if()
    }
}
#endif // version

#if version==2
void 
bst_insert_du(intptr_t x, bst* tp) {
    bst V0 = *tp;
    while(*tp) {
	struct _ADT_bst* *lp=&((struct _ADT_bst_node*)(*tp))->f0;
	intptr_t n=((struct _ADT_bst_node*)(*tp))->f1;
	struct _ADT_bst* *rp=&((struct _ADT_bst_node*)(*tp))->f2;
	if (x <= n)
            tp = lp;
        else
            tp = rp;
    }
    bst V2 = mt();
    bst V3 = mt();
    bst V1 = node(V2, x, V3);
    *tp=V1;
    return;
}
#endif // version

#if version==3
// prettier variant of version 2
void 
bst_insert_du(long x, tree *tp) {
    while(*tp) {
	if (x <= (*tp)->data)
            tp = &(*tp)->left;
        else
            tp = &(*tp)->right;
    }
    *tp = ADT_MALLOC(sizeof(struct tree_node));
    (*tp)->left = NULL;
    (*tp)->data = x;
    (*tp)->right = NULL;
}
// Alt version avoiding *tp so much
// void
// bst_insert_du(long x, tree *tp) {
//     tree t;
//     while((t = *tp) != NULL) {
//         if (x <= t->data)
//             tp = &t->left;
//         else
//             tp = &t->right;
//     }
//     t =
//     *tp = ADT_MALLOC(sizeof(struct tree_node));
//     t->left = NULL;
//     t->data = x;
//     t->right = NULL;
// }
#endif // version

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
