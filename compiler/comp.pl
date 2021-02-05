% Pawns -> C compiler
% reads foo.pns and writes foo.c and foo.adt (for type definitions)

:- ensure_loaded('pawns.pl').

% top level of compiler compilation
compile :-
    current_prolog_flag(argv, Argv),
    writeln(compiling-Argv),
    compile_argv(Argv),
    halt(0).

% compile given command line args
% XXX Seems to be some inconsistency with SWI-Prolog versions exactly
% what is included for argv and os_argv ...
% Also things have changed with strings versus lists of char codes etc
compile_argv(Argv) :-
    % writeq(argv(Argv)), nl,
    % XX allow some options ??
    ( append(_, ['--'|Files], Argv) -> % XX doesn't work????
        true
%     ; Argv = [_, _, _, _| Files] , Files = [_|_] ->
%         true
    ;
        % Argv = [_|Files]
        Argv = Files
    ),
    member(F, Files),
    name(F, FS),
    name('.pns', DPNS),
    ( append(BFS, DPNS, FS) ->
        true
    ;
        writeln('Error: ".pns" extension expected - file ignored'(F)),
        fail
    ),
    write('Compiling '),
    write(F),
    writeln(' to C ...'),
    input_file(F),
    share_anal,
    compile(BFS),
    fail.
compile_argv(_) :-
    writeln('Done').

% compilation of file (to C) - convenient for interactive testing
comp(F) :-
    input_file(F),
    name(F, FS),
    name('.pns', DPNS),
    append(BFS, DPNS, FS) ->
    compile(BFS).

% as above having read in file
compile(BNS) :-
    name('.c', DC),
    append(BNS, DC, F),
    name(File, F),
    tell(File),
    % XXX hack to strip of stuff before (*first* - should be last) "/"
    % XXXX still works with change in strings/char codes etc?
    ( append(_, [0'/|BNS1], BNS) ->
        true
    ;
        BNS1 = BNS
    ),
    name(BN1, BNS1),
    % XXX should have PAWNS_int = intptr_t + other similar things
    % and do more to avoid adtpp limitations causing warnings
    % some things now in pawns.h
    % writeln('typedef int *********************_void_ptr;'),
    % writeln('typedef void (*_func_ptr)(void*);'),
    % XX use <pawns.h> when its installed somewhere sensible
    write('#include "pawns.h"\n#include "'),
    write(BN1),
    writeln('.h"'),
    % hmm bit of a pain here: we need to output prototypes for
    % all builtins used in the code
    % somewhere we need to output/include the definitions also XXX
    % XXX need to add apply (or apply1, apply2 etc?)
    % XXX see also builtin_op
    % XXX best put in pawns.h with static __inline defns, or we can put
    % most stuff in libraries, implemented in C (see pns/io.pns)
    % writeln('intptr_t plus(intptr_t, intptr_t);'), % XXX
    % writeln('bool leq(intptr_t, intptr_t);'),
    % writeln('bool eq(intptr_t, intptr_t);'),
    % writeln('void print_int(intptr_t);'),
    % XXX need to know if things are exported so we can declare static
    (   mutable_global(MG),
        \+ member(MG, [io]),  % any other fake system globals??
        % globals are refs but we use the name to refer to the lvalue
        % rather than the rvalue since the ref itself is not mutable.
        % We do this by #defining the var to be the address
        % of a similarly named var which stores the mutable value.
        % XXX NOTE: we can do the same for local ref vars if the thing
        % they point to is not aliased to anything returned by the
        % function.  Since we have sharing analysis this is easy to
        % determine, but not yet implemented.
        nfdec_struct(MG, T),
        T = ref(T1),
        % write('static '),
        type_c_type('', T1),
        write(' '),
        write(MG),
        writeln('_VALUE;'),
        format('#define ~a (&~a_VALUE)\n', [MG, MG]),
        fail
    ;
        true
    ),  
    (   nfdec_struct(Fn, _),
        \+ builtin_func_arity(Fn, _),
        comp_fn_prototype(Fn),
        fail
    ;
        true
    ),  
    nl, nl,
    (    nfdec_struct(Fn, _),
        \+ builtin_func_arity(Fn, _),
        comp_fn(Fn),
        fail
    ;
        told
    ),
    name('.adt', DADT),
    append(BNS, DADT, F1),
    name(File1, F1),
    tell(File1),
    (   tdef(T, DCs), % XXX currently a hack for _closure type in pawns.pl
        % XXX toggle next two lines used to create stuff always included
        \+ builtin_tdef(T, _),
        % \+ member(T, [int, void, ref(_), '_type_param'(_)]),
        to_adt_defn(T, DCs),
        fail
    ;
        told
    ).  

% smash_type_vars_c(T) :-
%     ( var(T) ->
%         % T = 'pval_t' % typdef this to void* or intptr_t
%         T = int % XX
%     ;
%         T =.. [_|As],
%         map0(smash_type_vars_c, As)
%     ).


% write type defn in adtpp syntax
to_adt_defn(T, DCs) :-
    write('data '),
    type_adt_type(T),
    writeln(' {'),
    (   member(dcons(C, Ts), DCs),
        write('    '),
        write_fn(C),
        write('('),
        map0_comma(type_adt_type, Ts),
        writeln(');'),
        fail
    ;
        writeln('}')
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% abstract syntax -> C syntax (printed)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% print compiled function (C)
% XXX clean up duplication Pawns+C defns cases + printing prototypes.
comp_fn(Fn) :-
    % writeln('// compiling'(Fn)),
    func_arity(Fn, Arity),
    functor(LHS, Fn, Arity),
    % XXX avoid func_arity above failing...???
    ( imported(Fn) ->
        write('static __inline ')
    ;
        true
    ),
    ( extern_fn(LHS) ->
        true
    ; c_fn_def(LHS, Def) ->
        nfdec_struct(Fn, T),
        smash_type_params(T),
        extract_ret_type(Arity, T, TFArgs, TFR),
        type_c_type('', TFR),
        nl,
        LHS =.. [Fn|Args],
        write(Fn),
        write('('),
        map2(pair, TFArgs, Args, TPs),
        params_c_params(TPs),
        % map0_comma(write, Args1),
        write(')'),
        % write(LHS),
        map0(put, Def),
        nl, nl
    ;
        comp_fn1(Fn, Arity)
    ).

% as above for fn defined in Pawns
comp_fn1(Fn, Arity) :-
    % XX dodgey reset of var numbers so we (should) avoid
    % clashing with vars generated in pass which converts to canonical
    % form.  We use this for HO applications to too many args.  Could
    % be dealt with by earlier pass but the code there is a real mess
    % and its more of a compiler thing...
    retractall(var_number(_)),
    assert(var_number(1000)),
    nfdec_struct(Fn, T),
    % func_arity(Fn, Arity), % delete??
    fn_def_struct(Fn, Args, Stat),
    smash_type_params(T),
    extract_ret_type(Arity, T, TFArgs, TFR),
    type_c_type('', TFR),
    nl,
    write_fn(Fn), % XX shouldn't be redefining builtins
    write('('),
    map('vp(X,_),X', Args, Args1),
    map2(pair, TFArgs, Args1, TPs),
    params_c_params(TPs),
    % map0_comma(write, Args1),
    write(') {\n'),
    % traverse Stat and gather all wo(WOIs) annotations
    wo_globs(Stat, GVs),
    save_globs(GVs),
%     stat_eqlhss(Stat, EqLs, []),
%     sort(EqLs, EqLs1), % remove dups
%     map(eqlhs_type_var, EqLs1, TVs),
%     map0(to_var_dec, TVs),
    stat_c_stat(4, GVs, Stat),
    write('}\n\n').

% list of write only global vars introduced in statement
wo_globs(Stat, GVs) :-
    ( setof(GV, wo_mem_stat(GV, Stat), GVs) ->
        true
    ;
        GVs = []
    ).

% global var introduced in statement (generator)
wo_mem_stat(GV, C0-_) :-
    C0 = seq(Sa0, Sb0),
    (   wo_mem_stat(GV, Sa0)
    ;
        wo_mem_stat(GV, Sb0)
    ).
wo_mem_stat(GV, C0-_) :-
    C0 = cases(_, Cases0),
    wo_mem_case(GV, Cases0).
% wo_mem_stat(_GV, eq_var(Vl, Vr)-Ann0) :-
% wo_mem_stat(_GV, eq_deref(Vl, Vr)-Ann0) :-
% wo_mem_stat(_GV, deref_eq(Vl, Vr)-Ann0) :-
% wo_mem_stat(_GV, assign(Vl, Vr)-_) :-
% wo_mem_stat(GV, C-Ann0) :-
%     C = var_stat(V),
% wo_mem_stat(__GV, C-_) :-
%     C = empty_stat. % not needed?
% wo_mem_stat(_GV, C-Ann0) :-
%     C = eq_dc(Vl, DC, _, Args),
wo_mem_stat(GV, C-Ann0) :-
    C = eq_sapp(_, _, _),
    member(wo(GVs), Ann0),
    member(GV, GVs).
wo_mem_stat(GV, C-Ann0) :-
    C = eq_papp(_, _, _),
    member(wo(GVs), Ann0), % can't happen??
    member(GV, GVs).
wo_mem_stat(GV, C-Ann0) :-
    C = eq_app(_, _, _),
    member(wo(GVs), Ann0),
    member(GV, GVs).

% case -> C syntax
wo_mem_case(GV, case_def(S)) :-
    wo_mem_stat(GV, S).
wo_mem_case(GV, case_dc(_, _, _, S)) :-
    wo_mem_stat(GV, S).

% code to save current value of globals introduced in fn
save_globs(GVs) :-
    member(GV, GVs),
    nfdec_struct(GV, T),
    T = ref(T1),
    tab(4),
    type_c_type('', T1),
    write(' _OLDVAL_'),
    write(GV),
    write('= *'),
    write(GV),
    writeln(';'),
    fail.
save_globs(_).

% code to restore old value of globals introduced in fn
restore_globs(Ind, GVs) :-
    member(GV, GVs),
    tab(Ind),
    write('*'),
    write(GV),
    write(' = _OLDVAL_'),
    write(GV),
    writeln(';'),
    fail.
restore_globs(_, _).


'vp(X,_),X'(vp(X,_),X).

% print compiled function prototype only (C)
comp_fn_prototype(Fn) :-
    nfdec_struct(Fn, T),
    func_arity(Fn, Arity),
    length(Args1, Arity),
    LHS =.. [Fn|Args1],
    (   fn_def_struct(Fn, Args, _) ->
        map('vp(X,_),X', Args, Args1)
    ;
        (   c_fn_def(LHS, _)
        ;
            extern_fn(LHS)
        )
    ),
    smash_type_params(T),
    extract_ret_type(Arity, T, TFArgs, TFR),
    ( extern_fn(LHS) ->
        write('extern ')
    ; imported(Fn) ->
        write('static __inline ')
    ;
        true
    ),
    func_arity(Fn, Arity),
    type_c_type('', TFR),
    write(' '),
    write_fn(Fn),
    write('('),
    map2(pair, TFArgs, Args1, TPs),
    params_c_params(TPs),
    write(');\n').

pair(A, B, A-B).

% convert from var + type to C declaration (var may be '')
% Need to change some names, eg int -> intptr_t, bool -> PAWNS_bool
% (maybe we should use PAWNS_int and typedef it to intptr_t XXX)
% Handles ref and arrow types (XXX not curried - assumes all first arg
% of all outermost arrows are args); for other polymorphic
% types the args are ignored (we end up with casts or warnings).
% Maybe we should use void* or intptr_t for pretty much everything and
% use explicit casts all over the place????  Its nice to have C code
% well typed but adtpp doesn't support polymorphism properly as we use
% some hacks; currently its not so easy to know if an int var (for example)
% is an instance of a type var, so should be void* instead...
type_c_type(V, T) :-
    ( var(T) ->
        write('void *'),
        write(V)
    ; T = '_type_param'(_) ->
        write('void *'),
        write(V)
    ; T = int ->
        write('intptr_t '),
        write(V)
    ; T = bool ->
        write('PAWNS_bool '),
        write(V)
    ; T = arrow(_, _, _, _, _, _, _, _, _, _, _) ->
        % f::t1->t2->t3 is printed as t3 (*f)(t1,t2)
        extract_ret_type_max(_A, T, TAs, R),
        type_c_type('', R),
        write(' (*'),
        write(V),
        write(')('),
        ( TAs = [void] ->
            true
        ;
            map0_comma(type_c_type(''), TAs)
        ),
        write(')')
    ; T = ref(T1) ->
        type_c_type('', T1),
        write('*'),
        write(V)
    ;
        % just write top level of type - we know things are well typed
        % so for the C code we can just put casts everywhere
        T =..[F|_],
        write(F),
        write(' '),
        write(V)
    ).

% convert from type to type in adt system (just an identifier) -
% simplified version of above
type_adt_type(T) :-
    ( var(T) ->
        write('_void_ptr')
    % we have a special case for ref(void) because closures have args of
    % this type and adtpp can't handle * in arg types (currently)
    ; T = ref(void) ->
        write('_void_ptr')
    ; T = '_type_param'(_) ->
        write('_void_ptr')
    ; T = int ->
        write('intptr_t')
    ; T = bool ->
        write('PAWNS_bool')
    ; T = arrow(_, _, _, _, _, _, _, _, _, _, _) ->
        write('_closure')
    ; T = ref(T1) ->
        type_adt_type(T1),
        write('*')
    ;
        % just write top level of type - we know things are well typed
        % so for the C code we can just put casts everywhere
        T =..[F|_],
        write(F)
    ).

% print formal params (with types)
params_c_params(FAs) :-
    ( FAs = [void-_] ->
        true
    ;
        map0_comma(param_c_param, FAs)
    ).

% XXX clean this up - use map2 not pairs + map etc
% print formal param (with type); use _closure rather than real C
% function types
param_c_param(T-V) :-
    % type_c_type(V, T).
    type_adt_type(T),
    write(' '),
    write(V).

% % print var declaration
% to_var_dec(TV) :-
%     param_c_param(TV),
%     write(';\n').

% print internal representation as C syntax
% as_c((type TName ---> PTd), tdef(TName, CTs)) :-
% as_c(fdec(PT, RT, _Pre, _Post), _fdec(PT, RT)).
as_c(fdef(_FH, FB)) :-
    % head_c_head(FH),
    stat_c_stat(4, [], FB).

% as above for cases
cases_eqlhss([]) --> [].
cases_eqlhss([case(_, S)|Cs]) -->
    stat_eqlhss(S),
    cases_eqlhss(Cs).

% function definition -> C syntax
% head_c_head(H) :-
%     H =.. [F|As],
%     map(atom_var, As, Vs),
%     MH =.. [F|Vs].

% statement -> C syntax
% indentation added to make it more human readable
% list of write-only vars is passed in so they can be restored just
% before return statement
% We use memberchk(typed(T), Ann0) rather than member because with explicit
% type annotations in the source there can be more than on typed/1
% annotation (XXX probably should fix this?)
stat_c_stat(Ind, GVs, C0-_) :-
    C0 = seq(Sa0, Sb0),
    stat_c_stat(Ind, GVs, Sa0),
    stat_c_stat(Ind, GVs, Sb0).
stat_c_stat(Ind, GVs, C0-Ann0) :-
    C0 = cases(V, Cases0),
    memberchk(typed(T), Ann0),
    tab(Ind),
    write('switch_'),
    type_adt_type(T),
    writeln(''(V)),
    map0(case_c_case(Ind, GVs), Cases0),
    tab(Ind),
    writeln('end_switch()').
stat_c_stat(Ind, _GVs, eq_var(Vl, Vr)-Ann0) :-
    memberchk(typed(T), Ann0),
    ( T = void -> % just ignore v = void
        true
    ;
        tab(Ind),
        type_adt_type(T),
        write(' '),
        write(Vl),
        write(' = '),
        write(Vr),
        writeln(;)
    ).
stat_c_stat(Ind, _GVs, eq_deref(Vl, Vr)-Ann0) :-
    memberchk(typed(T), Ann0),
    % ( T = void -> % just ignore v = *voidp % XXX??
    tab(Ind),
    type_adt_type(T),
    write(' '),
    write(Vl),
    write(' = *'),
    write(Vr),
    writeln(;).
stat_c_stat(Ind, GVs, deref_eq(Vl, Vr)-Ann0) :-
    % *statevar = v is compiled as *!statevar := v
    ( mutable_global(Vl) ->
        stat_c_stat(Ind, GVs, assign(Vl, Vr)-Ann0)
    ;
        memberchk(typed(T), Ann0),
        % ( T = void -> % just ignore *v = void % XXX??
        tab(Ind),
        type_adt_type(ref(T)),
        write(' '),
        write(Vl),
        write(' = ('),
        type_adt_type(T),
        writeln('*)ADT_MALLOC(sizeof(void*));'),
        tab(Ind),
        write(*Vl = Vr),
        writeln(;)
    ).
stat_c_stat(Ind, _GVs, assign(Vl, Vr)-_) :-
    % ( T = void -> % just ignore v := void % XXX??
    tab(Ind),
    write(*Vl = Vr),
    writeln(;).
stat_c_stat(Ind, GVs, C-Ann0) :-
    C = var_stat(V),
    ( member(last_stat, Ann0) ->
        restore_globs(Ind, GVs),
        memberchk(typed(T), Ann0),
        tab(Ind),
        write(return),
        ( T = void ->
            true
        ;
            write(''(V))
        ),
        writeln(;)
%     ; memberchk(typed(arrow(_, _, _, _, _, _, _, _, _, _, _)), Ann0) ->
%         % must be function pointer but there are no args
%         write('(*'),
%         write(V),
%         writeln(')();)')
    ;
        % can ignore
        true
    ).
%     % we allow var::type "statements" and treat them as declarations
%     % they must come before the var is defined
%     ( member(typed(TV), Ann0) ->
%     ;
%     ).
stat_c_stat(_Ind, _GVs, C-_) :-
    C = empty_stat. % not needed?
stat_c_stat(Ind, _GVs, C-Ann0) :-
    C = eq_dc(Vl, DC, _, Args),
    memberchk(typed(T), Ann0),
    ( T = void -> % just ignore v = void
        true
    ;
        tab(Ind),
        type_adt_type(T),
        write(' '),
        write(Vl),
        write(' = '),
        write_fn(DC),
        ( number(DC) ->
            writeln(';')
        ;
            write('('),
            map0_comma(write, Args),
            writeln(');')
        )
    ).
stat_c_stat(Ind, _GVs, C-Ann0) :-
    C = eq_sapp(Vl, F, Args),
    memberchk(typed(T), Ann0),
    tab(Ind),
    ( T = void ->
        true
    ;
        type_adt_type(T),
        write(' '),
        write(Vl),
        write(' = ')
    ),
    write_fn(F),
    write('('),
    ( member(typed_rhs(arrow(void, _, _, _, _, _, _, _, _, _, _)), Ann0) ->
        true
    ;
        map0_comma(write, Args)
    ),
    write(')'),
    writeln(';').
stat_c_stat(Ind, _GVs, C-_) :-
    C = eq_papp(Vl, F, Args),
    % XXX what do we do about void->T functions in closures?
    % maybe have separate data constructor for them
    func_arity(F, Arity),
    ( Args = [] ->
        tab(Ind),
        write('_closure '),
        write(Vl),
        write(' = _cl0(&'), % XXX closure rep will change
        write_fn(F),
        write(', '),
        write(Arity),
        writeln(');')
    ;
        eq_papp_c(Ind, Vl, F, Arity, Args)
    ).
stat_c_stat(Ind, _GVs, C-Ann0) :-
    C = eq_app(Vl, F, Args),
    % XXX what do we do about void->T functions in closures?
    % maybe have separate data constructor for them
    memberchk(typed(T), Ann0),
    eq_app_c(Ind, T, Vl, F, Args).
%     tab(Ind),
%     ( T = void ->
%         write('(*'),
%         write_fn(F),
%         write(')')
%     ;
%         type_c_type(Vl, T),
%         write(' = '),
%         write('(*'),
%         write_fn(F),
%         write(')')
%     ),
%     write('('),
%     ( member(typed_rhs(arrow(void, _, _, _, _, _, _, _, _, _, _)), Ann0) ->
%         true
%     ;
%         map0_comma(write, Args)
%     ),
%     writeln(');').

% case -> C syntax
case_c_case(Ind, GVs, case_def(S)) :-
    tab(Ind),
    writeln('default()'),
    Ind1 is Ind + 4,
    stat_c_stat(Ind1, GVs, S).
case_c_case(Ind, GVs, case_dc(F, _, PAs, S)) :-
    tab(Ind),
    pat_c_pat(F, PAs),
    Ind1 is Ind + 4,
    stat_c_stat(Ind1, GVs, S).

% pattern -> C syntax
pat_c_pat(F, PAs) :-
    write('case_'),
    write_fn(F), % might have operators which are data constructors
    write('_ptr'),
    write('('),
    map0_comma(write, PAs),
    writeln(')').

% write C code for application of var to >=1 arg
% XXX specialise to use more closure data constructors and apply2 etc
% (currently apply does all the work) when available
eq_papp_c(Ind, Vl, F, Arity, Args) :-
    ( Args = [A] ->
        tab(Ind),
        write('_closure '),
        write(Vl),
        write(' = apply(_cl0(&'),
        write_fn(F),
        write(', '),
        write(Arity),
        write('), '),
        write(A),
        writeln(');')
    ;
        fresh_var(VF),
        Args = [A|Args1],
        eq_papp_c(Ind, VF, F, Arity, [A]),
        eq_app_c(Ind, '_closure', Vl, VF, Args1)
    ).

% write application of var to one or more args
% XXX specialise when apply2 etc are available
% XXX need to handle void/no arg(?)
eq_app_c(Ind, T, Vl, F, Args) :-
    ( (T \= void, Args = [A]) ->
        tab(Ind),
        type_adt_type(T),
        write(' '),
        write(Vl = apply(F, A)),
        writeln(';')
    ; (T = void, Args = [A]) ->
        tab(Ind),
        write(apply(F, A)),
        writeln(';')
    ;
        fresh_var(VF),
        append(Args1, [LA], Args),
        eq_app_c(Ind, '_closure', VF, F, Args1),
        eq_app_c(Ind, T, Vl, VF, [LA])
    ).
        
% renaming of builtin operators etc (fails for other things)
builtin_op('+', plus).
builtin_op('-', minus).
builtin_op('*', times).  % need care with overloading
builtin_op('/', div).
builtin_op('==', eq).
builtin_op('<=', leq).
builtin_op(true, 'PAWNS_true'). % avoid overloading with C
builtin_op(false, 'PAWNS_false').
% ... XXX see also compile/1
% Possibly should have compiler code to inline such things, or std lib
% which has all these things (with names like plus above) export_imp
% XXX nice to have short-circuited &&, || - a bit tricky!

% write function name (builtin ops need renaming)
write_fn(F) :-
    ( builtin_op(F, F1) ->
        write(F1)
    ;
        write(F)
    ).

cc :- [comp].

/*
co(a=nil; *b = cons(42, a); **x = 1; *b := a; cases *b of (case nil: *b
:= a; a case cons(h, *t): *t := nil; a)).


comp_fn(Fn).
comp_fn_prototype(Fn).

comp('eval.pns').
comp('wam.pns').
comp('isort.pns').
comp('bst_poly.pns').
comp('bst.pns').
comp('pbst.pns').
comp('cord.pns').
comp('cord_poly.pns').
comp('ho.pns').
comp('imp.pns').


*/

