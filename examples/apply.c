typedef void *_void_ptr;
typedef void (*_func_ptr)(void*);
#include "apply.h"

// need to generalise this to any number of closure args (ie, a list)
// + we need to support application to multiple args.
// can specialise representation (eg) as follows (we have a certain
// number of closure args and need a certain number of extra args):
// _cl0_1(f), _cl0_2(f), _cl1_1(f,cla1), _cl2_2(f,cla1,cla2),
// cl0(f,n), _cl1(f,n,cla1), _cl2(f,n,cla1,cla2),
// cl(f,n,cla1,cla2,cas) -- (may want length of list cas also?)
// Also, have apply, apply2, apply3? and for more args use nested calls
// to these (less efficient but we have to stop somewhere; have a flag
// somewhere so we can increase this).
// Want general case + specialised ones.  Hard to do general case with C
// - we need a call with N arguments, for unbounded N.  Could specify a
// maximum arity for HO calls; user can generally group arguments as a
// tuple if needed.

void *
apply(_closure cl, void *a1) {
    _func_ptr r;
    void *ca1, *ca2, *ca3, *ca4;
    intptr_t aty;

    switch__closure(cl)
    case__cl0(f, aty)
        if (aty==1) {
            return (*(void*(*)(void*))f)(a1);
        } else
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

