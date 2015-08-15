#include "pawns.h"
#include "bst.h"
intptr_t  counter_VALUE;
#define counter (&counter_VALUE)
list  ints1();
bst  list_bst(list xs);
void  list_bst_du(list xs, bst* tp);
void  bst_insert_du(intptr_t x, bst* tp);
intptr_t  bst_sum(bst t);
void  init_counter(intptr_t n);
void  assign_counter(intptr_t n);
void  add_to_counter(intptr_t n);
void  bst_sum1(bst t);
void  print_tree(bst t);
void  print_ints(list t);
static __inline list  map(_closure f, list mbs);
static __inline list  map2(_closure f, list mbs, list mcs);
static __inline intptr_t  inc(intptr_t n);
static __inline list  incs(list is);
static __inline list  add_lists(list xs, list ys);


list 
ints1() {
    intptr_t V1 = 4;
    intptr_t V3 = 2;
    intptr_t V5 = 1;
    intptr_t V7 = 3;
    list V8 = nil();
    list V6 = cons(V7, V8);
    list V4 = cons(V5, V6);
    list V2 = cons(V3, V4);
    list V0 = cons(V1, V2);
    return(V0);
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

intptr_t 
bst_sum(bst t) {
    intptr_t  _OLDVAL_counter= *counter;
    intptr_t V1 = 0;
    init_counter(V1);
    bst_sum1(t);
    intptr_t V3 = *counter;
    *counter = _OLDVAL_counter;
    return(V3);
}

void 
init_counter(intptr_t n) {
    *counter=n;
}

void 
assign_counter(intptr_t n) {
    *counter=n;
}

void 
add_to_counter(intptr_t n) {
    intptr_t V1 = *counter;
    intptr_t V0 = plus(V1, n);
    *counter=V0;
}

void 
bst_sum1(bst t) {
    switch_bst(t)
    case_mt_ptr()
        return;
    case_node_ptr(V1, V2, V3)
        bst r = *V3;
        intptr_t n = *V2;
        bst l = *V1;
        bst_sum1(l);
        add_to_counter(n);
        intptr_t V7 = bst_sum(r);
        add_to_counter(V7);
        return;
    end_switch()
}

void 
print_tree(bst t) {
    switch_bst(t)
    case_mt_ptr()
        return;
    case_node_ptr(V1, V2, V3)
        bst r = *V3;
        intptr_t n = *V2;
        bst l = *V1;
        print_tree(l);
        print_int(n);
        print_tree(r);
        return;
    end_switch()
}

void 
print_ints(list t) {
    switch_list(t)
    case_nil_ptr()
        return;
    case_cons_ptr(V1, V2)
        list r = *V2;
        intptr_t n = *V1;
        print_int(n);
        print_ints(r);
        return;
    end_switch()
}

static __inline list 
map(_closure f, list mbs) {
    switch_list(mbs)
    case_nil_ptr()
        list V0 = nil();
        return(V0);
    case_cons_ptr(V1, V2)
        list mbs1 = *V2;
        intptr_t mb = *V1;
        intptr_t V4=apply(f,mb);
        list V5 = map(f, mbs1);
        list V3 = cons(V4, V5);
        return(V3);
    end_switch()
}

static __inline list 
map2(_closure f, list mbs, list mcs) {
    switch_list(mbs)
    case_nil_ptr()
        list V0 = nil();
        return(V0);
    case_cons_ptr(V1, V2)
        list mbs1 = *V2;
        intptr_t mb = *V1;
        switch_list(mcs)
        case_nil_ptr()
            list V3 = nil();
            return(V3);
        case_cons_ptr(V4, V5)
            list mcs1 = *V5;
            intptr_t mc = *V4;
            _closure V1000=apply(f,mb);
            intptr_t V7=apply(V1000,mc);
            list V8 = map2(f, mbs1, mcs1);
            list V6 = cons(V7, V8);
            return(V6);
        end_switch()
    end_switch()
}

static __inline intptr_t 
inc(intptr_t n) {
    intptr_t V1 = 10;
    intptr_t V0 = plus(n, V1);
    return(V0);
}

static __inline list 
incs(list is) {
    intptr_t V2 = 20;
    _closure V1 = apply(_cl0(&plus, 2), V2);
    list V0 = map(V1, is);
    return(V0);
}

static __inline list 
add_lists(list xs, list ys) {
    _closure V1 = _cl0(&plus, 2);
    list V0 = map2(V1, xs, ys);
    return(V0);
}

