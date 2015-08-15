#include <stdint.h>
#include <stdlib.h>
// typedef char *c_string;
#define end_switch() }}}}
#define default() break;}} default: {{
#define else() } else {
#define end_if() }}
#define LOW_BIT_USED 7
/***************************/
typedef struct _ADT__closure{} *_closure;
#define _closure_T_NUM_CONST (1) 
#define _closure_T_NUM_NONCONST (5) 
#define _closure_constructorNum(v) \
(( _closure_T_NUM_NONCONST>0 && v > _closure_T_NUM_CONST-1 ?  \
 ( _closure_T_NUM_NONCONST==1 ?  _closure_T_NUM_CONST   : \
(( _closure_T_NUM_NONCONST > (LOW_BIT_USED + 1))  && ((v&LOW_BIT_USED) == (LOW_BIT_USED))  )  ?   \
 (*(int*)((uintptr_t)_ADT_v-LOW_BIT_USED)) + _closure_T_NUM_CONST  : \
((v&(LOW_BIT_USED)) + _closure_T_NUM_CONST)) : v ) )

static __inline void free__closure(_closure v);
#define switch__closure(v) \
{_closure __closure_tchk, _ADT_v=(v); \
int t = _closure_constructorNum((uintptr_t)(_ADT_v)); \
switch(t) {{{


/******************************************************************************/
static __inline void free__closure(_closure v){
	if ((uintptr_t)(v) >= 1){
		free((void*)((uintptr_t)v&~LOW_BIT_USED));
	}
}

;
struct _ADT__closure__cl_delete_this_when_adtpp_fixed {};
#define if__cl_delete_this_when_adtpp_fixed(v) \
{_closure _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define else_if__cl_delete_this_when_adtpp_fixed() \
} else if (((uintptr_t)(_ADT_v))==0) {
#define if__cl_delete_this_when_adtpp_fixed_ptr(v) \
{_closure _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define case__cl_delete_this_when_adtpp_fixed() \
break;}} case 0: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; 
#define case__cl_delete_this_when_adtpp_fixed_ptr() \
break;}} case 0: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; 

static __inline _closure _cl_delete_this_when_adtpp_fixed(){
	struct _ADT__closure__cl_delete_this_when_adtpp_fixed *v=(struct _ADT__closure__cl_delete_this_when_adtpp_fixed*)0;
	return (_closure)((uintptr_t)v);
}
;
struct _ADT__closure__cl0 {
    struct _ADT__closure* f0;
    intptr_t f1;};
#define if__cl0(v, v0, v1) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==0) {\
struct _ADT__closure* v0=((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f0; \
intptr_t v1=((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f1; 
#define else_if__cl0(v0, v1) \
} else if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==0)  {\
struct _ADT__closure* v0=((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f0; \
intptr_t v1=((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f1; 
#define if__cl0_ptr(v, v0, v1) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==0)  {\
struct _ADT__closure* *v0=&((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f1; 
#define case__cl0(v0, v1) \
break;}} case 1: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* v0=((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f0; \
intptr_t v1=((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f1; 
#define case__cl0_ptr(v0, v1) \
break;}} case 1: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* *v0=&((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl0*)((uintptr_t)_ADT_v-0))->f1; 

static __inline _closure _cl0(struct _ADT__closure* v0, intptr_t v1){
	struct _ADT__closure__cl0 *v=(struct _ADT__closure__cl0*)malloc(sizeof(struct _ADT__closure__cl0));
	v->f0=v0; 
	v->f1=v1; 
	return (_closure)(0+(uintptr_t)v);
}
;
struct _ADT__closure__cl1 {
    struct _ADT__closure* f0;
    intptr_t f1;
    _void_ptr f2;};
#define if__cl1(v, v0, v1, v2) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==1) {\
struct _ADT__closure* v0=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f0; \
intptr_t v1=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f1; \
_void_ptr v2=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f2; 
#define else_if__cl1(v0, v1, v2) \
} else if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==1)  {\
struct _ADT__closure* v0=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f0; \
intptr_t v1=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f1; \
_void_ptr v2=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f2; 
#define if__cl1_ptr(v, v0, v1, v2) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==1)  {\
struct _ADT__closure* *v0=&((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f2; 
#define case__cl1(v0, v1, v2) \
break;}} case 2: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* v0=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f0; \
intptr_t v1=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f1; \
_void_ptr v2=((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f2; 
#define case__cl1_ptr(v0, v1, v2) \
break;}} case 2: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* *v0=&((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl1*)((uintptr_t)_ADT_v-1))->f2; 

static __inline _closure _cl1(struct _ADT__closure* v0, intptr_t v1, _void_ptr v2){
	struct _ADT__closure__cl1 *v=(struct _ADT__closure__cl1*)malloc(sizeof(struct _ADT__closure__cl1));
	v->f0=v0; 
	v->f1=v1; 
	v->f2=v2; 
	return (_closure)(1+(uintptr_t)v);
}
;
struct _ADT__closure__cl2 {
    struct _ADT__closure* f0;
    intptr_t f1;
    _void_ptr f2;
    _void_ptr f3;};
#define if__cl2(v, v0, v1, v2, v3) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==2) {\
struct _ADT__closure* v0=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f0; \
intptr_t v1=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f1; \
_void_ptr v2=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f2; \
_void_ptr v3=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f3; 
#define else_if__cl2(v0, v1, v2, v3) \
} else if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==2)  {\
struct _ADT__closure* v0=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f0; \
intptr_t v1=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f1; \
_void_ptr v2=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f2; \
_void_ptr v3=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f3; 
#define if__cl2_ptr(v, v0, v1, v2, v3) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==2)  {\
struct _ADT__closure* *v0=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f2; \
_void_ptr *v3=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f3; 
#define case__cl2(v0, v1, v2, v3) \
break;}} case 3: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* v0=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f0; \
intptr_t v1=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f1; \
_void_ptr v2=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f2; \
_void_ptr v3=((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f3; 
#define case__cl2_ptr(v0, v1, v2, v3) \
break;}} case 3: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* *v0=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f2; \
_void_ptr *v3=&((struct _ADT__closure__cl2*)((uintptr_t)_ADT_v-2))->f3; 

static __inline _closure _cl2(struct _ADT__closure* v0, intptr_t v1, _void_ptr v2, _void_ptr v3){
	struct _ADT__closure__cl2 *v=(struct _ADT__closure__cl2*)malloc(sizeof(struct _ADT__closure__cl2));
	v->f0=v0; 
	v->f1=v1; 
	v->f2=v2; 
	v->f3=v3; 
	return (_closure)(2+(uintptr_t)v);
}
;
struct _ADT__closure__cl3 {
    struct _ADT__closure* f0;
    intptr_t f1;
    _void_ptr f2;
    _void_ptr f3;
    _void_ptr f4;};
#define if__cl3(v, v0, v1, v2, v3, v4) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==3) {\
struct _ADT__closure* v0=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f0; \
intptr_t v1=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f1; \
_void_ptr v2=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f2; \
_void_ptr v3=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f3; \
_void_ptr v4=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f4; 
#define else_if__cl3(v0, v1, v2, v3, v4) \
} else if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==3)  {\
struct _ADT__closure* v0=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f0; \
intptr_t v1=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f1; \
_void_ptr v2=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f2; \
_void_ptr v3=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f3; \
_void_ptr v4=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f4; 
#define if__cl3_ptr(v, v0, v1, v2, v3, v4) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==3)  {\
struct _ADT__closure* *v0=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f2; \
_void_ptr *v3=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f3; \
_void_ptr *v4=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f4; 
#define case__cl3(v0, v1, v2, v3, v4) \
break;}} case 4: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* v0=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f0; \
intptr_t v1=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f1; \
_void_ptr v2=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f2; \
_void_ptr v3=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f3; \
_void_ptr v4=((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f4; 
#define case__cl3_ptr(v0, v1, v2, v3, v4) \
break;}} case 4: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* *v0=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f2; \
_void_ptr *v3=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f3; \
_void_ptr *v4=&((struct _ADT__closure__cl3*)((uintptr_t)_ADT_v-3))->f4; 

static __inline _closure _cl3(struct _ADT__closure* v0, intptr_t v1, _void_ptr v2, _void_ptr v3, _void_ptr v4){
	struct _ADT__closure__cl3 *v=(struct _ADT__closure__cl3*)malloc(sizeof(struct _ADT__closure__cl3));
	v->f0=v0; 
	v->f1=v1; 
	v->f2=v2; 
	v->f3=v3; 
	v->f4=v4; 
	return (_closure)(3+(uintptr_t)v);
}
;
struct _ADT__closure__cl4 {
    struct _ADT__closure* f0;
    intptr_t f1;
    _void_ptr f2;
    _void_ptr f3;
    _void_ptr f4;
    _void_ptr f5;};
#define if__cl4(v, v0, v1, v2, v3, v4, v5) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==4) {\
struct _ADT__closure* v0=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f0; \
intptr_t v1=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f1; \
_void_ptr v2=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f2; \
_void_ptr v3=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f3; \
_void_ptr v4=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f4; \
_void_ptr v5=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f5; 
#define else_if__cl4(v0, v1, v2, v3, v4, v5) \
} else if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==4)  {\
struct _ADT__closure* v0=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f0; \
intptr_t v1=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f1; \
_void_ptr v2=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f2; \
_void_ptr v3=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f3; \
_void_ptr v4=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f4; \
_void_ptr v5=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f5; 
#define if__cl4_ptr(v, v0, v1, v2, v3, v4, v5) \
{_closure _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1 && ((uintptr_t)(_ADT_v)&LOW_BIT_USED)==4)  {\
struct _ADT__closure* *v0=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f2; \
_void_ptr *v3=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f3; \
_void_ptr *v4=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f4; \
_void_ptr *v5=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f5; 
#define case__cl4(v0, v1, v2, v3, v4, v5) \
break;}} case 5: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* v0=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f0; \
intptr_t v1=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f1; \
_void_ptr v2=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f2; \
_void_ptr v3=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f3; \
_void_ptr v4=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f4; \
_void_ptr v5=((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f5; 
#define case__cl4_ptr(v0, v1, v2, v3, v4, v5) \
break;}} case 5: {{_closure _SW_tchk=__closure_tchk;}{char __closure_tchk; \
struct _ADT__closure* *v0=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f0; \
intptr_t *v1=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f1; \
_void_ptr *v2=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f2; \
_void_ptr *v3=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f3; \
_void_ptr *v4=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f4; \
_void_ptr *v5=&((struct _ADT__closure__cl4*)((uintptr_t)_ADT_v-4))->f5; 

static __inline _closure _cl4(struct _ADT__closure* v0, intptr_t v1, _void_ptr v2, _void_ptr v3, _void_ptr v4, _void_ptr v5){
	struct _ADT__closure__cl4 *v=(struct _ADT__closure__cl4*)malloc(sizeof(struct _ADT__closure__cl4));
	v->f0=v0; 
	v->f1=v1; 
	v->f2=v2; 
	v->f3=v3; 
	v->f4=v4; 
	v->f5=v5; 
	return (_closure)(4+(uintptr_t)v);
}

/***************************/
typedef struct _ADT_pair{} *pair;
#define pair_T_NUM_CONST (0) 
#define pair_T_NUM_NONCONST (1) 
#define pair_constructorNum(v) \
(( pair_T_NUM_NONCONST>0 && v > pair_T_NUM_CONST-1 ?  \
 ( pair_T_NUM_NONCONST==1 ?  pair_T_NUM_CONST   : \
(( pair_T_NUM_NONCONST > (LOW_BIT_USED + 1))  && ((v&LOW_BIT_USED) == (LOW_BIT_USED))  )  ?   \
 (*(int*)((uintptr_t)_ADT_v-LOW_BIT_USED)) + pair_T_NUM_CONST  : \
((v&(LOW_BIT_USED)) + pair_T_NUM_CONST)) : v ) )

static __inline void free_pair(pair v);
#define switch_pair(v) \
{pair _pair_tchk, _ADT_v=(v); \
int t = pair_constructorNum((uintptr_t)(_ADT_v)); \
switch(t) {{{


/******************************************************************************/
static __inline void free_pair(pair v){
	if ((uintptr_t)(v) >= 0){
		free((void*)((uintptr_t)v));
	}
}

;
struct _ADT_pair_t2 {
    _void_ptr f0;
    _void_ptr f1;};
#define if_t2(v, v0, v1) \
{pair _ADT_v=(v);if (1) {\
_void_ptr v0=((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f0; \
_void_ptr v1=((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f1; 
#define else_if_t2(v0, v1) \
} else if (1) {\
_void_ptr v0=((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f0; \
_void_ptr v1=((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f1; 
#define if_t2_ptr(v, v0, v1) \
{pair _ADT_v=(v);if (1) {\
_void_ptr *v0=&((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f0; \
_void_ptr *v1=&((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f1; 
#define case_t2(v0, v1) \
break;}} case 0: {{pair _SW_tchk=_pair_tchk;}{char _pair_tchk; \
_void_ptr v0=((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f0; \
_void_ptr v1=((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f1; 
#define case_t2_ptr(v0, v1) \
break;}} case 0: {{pair _SW_tchk=_pair_tchk;}{char _pair_tchk; \
_void_ptr *v0=&((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f0; \
_void_ptr *v1=&((struct _ADT_pair_t2*)((uintptr_t)_ADT_v-0))->f1; 

static __inline pair t2(_void_ptr v0, _void_ptr v1){
	struct _ADT_pair_t2 *v=(struct _ADT_pair_t2*)malloc(sizeof(struct _ADT_pair_t2));
	v->f0=v0; 
	v->f1=v1; 
	return (pair)(0+(uintptr_t)v);
}

/***************************/
typedef struct _ADT_maybe{} *maybe;
#define maybe_T_NUM_CONST (1) 
#define maybe_T_NUM_NONCONST (1) 
#define maybe_constructorNum(v) \
(( maybe_T_NUM_NONCONST>0 && v > maybe_T_NUM_CONST-1 ?  \
 ( maybe_T_NUM_NONCONST==1 ?  maybe_T_NUM_CONST   : \
(( maybe_T_NUM_NONCONST > (LOW_BIT_USED + 1))  && ((v&LOW_BIT_USED) == (LOW_BIT_USED))  )  ?   \
 (*(int*)((uintptr_t)_ADT_v-LOW_BIT_USED)) + maybe_T_NUM_CONST  : \
((v&(LOW_BIT_USED)) + maybe_T_NUM_CONST)) : v ) )

static __inline void free_maybe(maybe v);
#define switch_maybe(v) \
{maybe _maybe_tchk, _ADT_v=(v); \
int t = maybe_constructorNum((uintptr_t)(_ADT_v)); \
switch(t) {{{


/******************************************************************************/
static __inline void free_maybe(maybe v){
	if ((uintptr_t)(v) >= 1){
		free((void*)((uintptr_t)v));
	}
}

;
struct _ADT_maybe_nothing {};
#define if_nothing(v) \
{maybe _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define else_if_nothing() \
} else if (((uintptr_t)(_ADT_v))==0) {
#define if_nothing_ptr(v) \
{maybe _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define case_nothing() \
break;}} case 0: {{maybe _SW_tchk=_maybe_tchk;}{char _maybe_tchk; 
#define case_nothing_ptr() \
break;}} case 0: {{maybe _SW_tchk=_maybe_tchk;}{char _maybe_tchk; 

static __inline maybe nothing(){
	struct _ADT_maybe_nothing *v=(struct _ADT_maybe_nothing*)0;
	return (maybe)((uintptr_t)v);
}
;
struct _ADT_maybe_just {
    _void_ptr f0;};
#define if_just(v, v0) \
{maybe _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1) {\
_void_ptr v0=((struct _ADT_maybe_just*)((uintptr_t)_ADT_v-0))->f0; 
#define else_if_just(v0) \
} else if ((uintptr_t)(_ADT_v) >= 1) {\
_void_ptr v0=((struct _ADT_maybe_just*)((uintptr_t)_ADT_v-0))->f0; 
#define if_just_ptr(v, v0) \
{maybe _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1) {\
_void_ptr *v0=&((struct _ADT_maybe_just*)((uintptr_t)_ADT_v-0))->f0; 
#define case_just(v0) \
break;}} case 1: {{maybe _SW_tchk=_maybe_tchk;}{char _maybe_tchk; \
_void_ptr v0=((struct _ADT_maybe_just*)((uintptr_t)_ADT_v-0))->f0; 
#define case_just_ptr(v0) \
break;}} case 1: {{maybe _SW_tchk=_maybe_tchk;}{char _maybe_tchk; \
_void_ptr *v0=&((struct _ADT_maybe_just*)((uintptr_t)_ADT_v-0))->f0; 

static __inline maybe just(_void_ptr v0){
	struct _ADT_maybe_just *v=(struct _ADT_maybe_just*)malloc(sizeof(struct _ADT_maybe_just));
	v->f0=v0; 
	return (maybe)(0+(uintptr_t)v);
}

/***************************/
typedef struct _ADT_list{} *list;
#define list_T_NUM_CONST (1) 
#define list_T_NUM_NONCONST (1) 
#define list_constructorNum(v) \
(( list_T_NUM_NONCONST>0 && v > list_T_NUM_CONST-1 ?  \
 ( list_T_NUM_NONCONST==1 ?  list_T_NUM_CONST   : \
(( list_T_NUM_NONCONST > (LOW_BIT_USED + 1))  && ((v&LOW_BIT_USED) == (LOW_BIT_USED))  )  ?   \
 (*(int*)((uintptr_t)_ADT_v-LOW_BIT_USED)) + list_T_NUM_CONST  : \
((v&(LOW_BIT_USED)) + list_T_NUM_CONST)) : v ) )

static __inline void free_list(list v);
#define switch_list(v) \
{list _list_tchk, _ADT_v=(v); \
int t = list_constructorNum((uintptr_t)(_ADT_v)); \
switch(t) {{{


/******************************************************************************/
static __inline void free_list(list v){
	if ((uintptr_t)(v) >= 1){
		free((void*)((uintptr_t)v));
	}
}

;
struct _ADT_list_nil {};
#define if_nil(v) \
{list _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define else_if_nil() \
} else if (((uintptr_t)(_ADT_v))==0) {
#define if_nil_ptr(v) \
{list _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define case_nil() \
break;}} case 0: {{list _SW_tchk=_list_tchk;}{char _list_tchk; 
#define case_nil_ptr() \
break;}} case 0: {{list _SW_tchk=_list_tchk;}{char _list_tchk; 

static __inline list nil(){
	struct _ADT_list_nil *v=(struct _ADT_list_nil*)0;
	return (list)((uintptr_t)v);
}
;
struct _ADT_list_cons {
    _void_ptr f0;
    struct _ADT_list* f1;};
#define if_cons(v, v0, v1) \
{list _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1) {\
_void_ptr v0=((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f0; \
struct _ADT_list* v1=((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f1; 
#define else_if_cons(v0, v1) \
} else if ((uintptr_t)(_ADT_v) >= 1) {\
_void_ptr v0=((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f0; \
struct _ADT_list* v1=((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f1; 
#define if_cons_ptr(v, v0, v1) \
{list _ADT_v=(v);if ((uintptr_t)(_ADT_v) >= 1) {\
_void_ptr *v0=&((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f0; \
struct _ADT_list* *v1=&((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f1; 
#define case_cons(v0, v1) \
break;}} case 1: {{list _SW_tchk=_list_tchk;}{char _list_tchk; \
_void_ptr v0=((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f0; \
struct _ADT_list* v1=((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f1; 
#define case_cons_ptr(v0, v1) \
break;}} case 1: {{list _SW_tchk=_list_tchk;}{char _list_tchk; \
_void_ptr *v0=&((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f0; \
struct _ADT_list* *v1=&((struct _ADT_list_cons*)((uintptr_t)_ADT_v-0))->f1; 

static __inline list cons(_void_ptr v0, struct _ADT_list* v1){
	struct _ADT_list_cons *v=(struct _ADT_list_cons*)malloc(sizeof(struct _ADT_list_cons));
	v->f0=v0; 
	v->f1=v1; 
	return (list)(0+(uintptr_t)v);
}

/***************************/
typedef struct _ADT_PAWNS_bool{} *PAWNS_bool;
#define PAWNS_bool_T_NUM_CONST (2) 
#define PAWNS_bool_T_NUM_NONCONST (0) 
#define PAWNS_bool_constructorNum(v) \
(( PAWNS_bool_T_NUM_NONCONST>0 && v > PAWNS_bool_T_NUM_CONST-1 ?  \
 ( PAWNS_bool_T_NUM_NONCONST==1 ?  PAWNS_bool_T_NUM_CONST   : \
(( PAWNS_bool_T_NUM_NONCONST > (LOW_BIT_USED + 1))  && ((v&LOW_BIT_USED) == (LOW_BIT_USED))  )  ?   \
 (*(int*)((uintptr_t)_ADT_v-LOW_BIT_USED)) + PAWNS_bool_T_NUM_CONST  : \
((v&(LOW_BIT_USED)) + PAWNS_bool_T_NUM_CONST)) : v ) )


#define switch_PAWNS_bool(v) \
{PAWNS_bool _PAWNS_bool_tchk, _ADT_v=(v); \
int t = PAWNS_bool_constructorNum((uintptr_t)(_ADT_v)); \
switch(t) {{{


/******************************************************************************/
;
struct _ADT_PAWNS_bool_PAWNS_false {};
#define if_PAWNS_false(v) \
{PAWNS_bool _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define else_if_PAWNS_false() \
} else if (((uintptr_t)(_ADT_v))==0) {
#define if_PAWNS_false_ptr(v) \
{PAWNS_bool _ADT_v=(v);if (((uintptr_t)(_ADT_v))==0) {
#define case_PAWNS_false() \
break;}} case 0: {{PAWNS_bool _SW_tchk=_PAWNS_bool_tchk;}{char _PAWNS_bool_tchk; 
#define case_PAWNS_false_ptr() \
break;}} case 0: {{PAWNS_bool _SW_tchk=_PAWNS_bool_tchk;}{char _PAWNS_bool_tchk; 

static __inline PAWNS_bool PAWNS_false(){
	struct _ADT_PAWNS_bool_PAWNS_false *v=(struct _ADT_PAWNS_bool_PAWNS_false*)0;
	return (PAWNS_bool)((uintptr_t)v);
}
;
struct _ADT_PAWNS_bool_PAWNS_true {};
#define if_PAWNS_true(v) \
{PAWNS_bool _ADT_v=(v);if (((uintptr_t)(_ADT_v))==1) {
#define else_if_PAWNS_true() \
} else if (((uintptr_t)(_ADT_v))==1) {
#define if_PAWNS_true_ptr(v) \
{PAWNS_bool _ADT_v=(v);if (((uintptr_t)(_ADT_v))==1) {
#define case_PAWNS_true() \
break;}} case 1: {{PAWNS_bool _SW_tchk=_PAWNS_bool_tchk;}{char _PAWNS_bool_tchk; 
#define case_PAWNS_true_ptr() \
break;}} case 1: {{PAWNS_bool _SW_tchk=_PAWNS_bool_tchk;}{char _PAWNS_bool_tchk; 

static __inline PAWNS_bool PAWNS_true(){
	struct _ADT_PAWNS_bool_PAWNS_true *v=(struct _ADT_PAWNS_bool_PAWNS_true*)1;
	return (PAWNS_bool)((uintptr_t)v);
}
