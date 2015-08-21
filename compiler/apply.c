// now copied to pawns.h

typedef void *_void_ptr;
typedef void (*_func_ptr)(void*);
#include "apply.h"

void *
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

