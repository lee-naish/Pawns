% *prototype* implementation of Pawns (tentative name)
% (Pointer Assignment With No Surprises, alt name is
% Flic - Functional Language Influenced by C)
% Read Prolog-ish syntax and convert to other forms
% (internal representation, C, ...)
% This file is too long and the structure within it is not understood -
% it should be broken up into separate modules etc...

% XXX need to FIX sharing analysis for cases ++ (see paper)

% XXX need to FIX checking of ! in statements: distinguish between
% direct and indirect: var shared with du arg must have ibang for type
% safety, even if it appears as another arg with dbang

% XXX bug if same var is used in multiple function arguments (including
% implicit args). Could write extra code to detect this or introduce
% fresh vars everywhere.  The latter probably simplifies other code but
% introduces more vars and equations.  If we remove dead vars from the
% analysis and use -O3 in compiling the C that shouldn't impact too much.

% XXX use read_term(X, [variable_names(Vs)]) for function prototypes and
% definitions and unifiy vars so we can cast vars to types including
% type vars in the prototype.

% XXX some hacking done related to name/2 etc due to the way string
% handling has changed in Prolog over the years.  Should just go with
% the modern way of doing things probably.

:- ensure_loaded(library(ordsets)).

% set up operators to enable OK syntax to be used (see *.pns)
% XX try to tweek these so we can declare vars locally with :: but no
% () (priority of :: should be low)
:- op(5, fx, (!)).
:- op(10, fy, (*)).
:- op(10, fy, (**)). % for multiple indirection
:- op(10, fy, (***)). % for multiple indirection
% :- op(10, fy, (****)). % three is enough...
% :- op(600, yfx, (!)).
:- op(750, yfx, (!)).
:- op(705, xfx, (:=)).
% :- op(700, xfx, (=)). % std
:- op(705, xfx, (=)). % shouldn't break things; allows a = 1<2
:- op(700, xfx, (<=)). % Prolog uses =<
:- op(1150, fx, (type)).
:- op(1180, xfx, (--->)). % XXX could we use simpler arrow??
% :- op(15, xfx, (::)).
:- op(1150, xfx, (::)). % XX ???
% Here we have sharing binding more tightly than ->, so sharing info is
% attached to innermost (rightmost) arrow.  Precedence of ';' is
% changed - see below
% :- op(1050, xfy, (->)). % std
:- op(1030, xfx, (implicit)).
:- op(950, fx, (ro)).
:- op(950, fx, (rw)).
:- op(950, fx, (wo)).
:- op(1045, xfx, (sharing)).
:- op(1040, xfx, (pre)).
:- op(1020, xfx, (post)).
% std precedence for ';' (temporarily overridden to read Pawns code,
% primarily so we don't need extra ()/{} around pre/postconditions which
% include ';'))
% we explicitly declare it here in case things go wrong and the
% temporary value hangs around
% XX? could lower numbers here and use {} around compound blocks in
% cases but need endcase indication
:- op(1100, xfy, (;)). % std
% :- op(1010, xfy, (;)).  % we use this temporarily
:- op(1195, fx, (case)).
:- op(1190, xfy, (case)).
:- op(1150, xfx, (:)).
:- op(800, fx, (cases)).
:- op(900, xfx, (of)).
% if-then-else - need {} around compound statements
:- op(996, xfy, (else)).
:- op(994, fx, (if)).
:- op(992, xfx, (then)).
% very basic module stuff
:- op(1190, fx, (import)).
:- op(1110, xfx, (from)).
:- op(1110, fx, (from)).
:- op(1190, fx, (export_name)).
:- op(1190, fx, (export_imp)).
:- op(600, fx, (as_C)).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Some top level stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% sharing analysis of file
% (faiure driven loop, fails at top level for convenience)
san(BN) :-
    input_file(BN),
    share_anal,
    writeln('OK'),
    fail.   % so we don't haver to hit return when testing

% as above having input the file
share_anal :-
    writeln('    .......'),
    nfdec_struct(Fn, _),
    \+ builtin_func_arity(Fn, _),
    \+ mutable_global(Fn),
    alias_fn(Fn),
    fail.  
share_anal :-
    writeln('    Sharing analysis completed\n').

% read source file and
% assert everything XX (should pass it around as state).
input_file(File) :-
    retractall(imported(_)),
    retractall(prog_dcons(_)),
    retractall(c_fn_def(_, _)),
    retractall(extern_fn(_)),
    retractall(func_arity(_, _)),
    retractall(fdef_struct(_, _, _)),
    retractall(nfdec_struct(_, _)),
    retractall(type_struct_c(_, _)),
    retractall(teqdef(_, _)),
    retractall(tdef(_, _)),
    retractall(mutable_global(_)),
    file_as(File, As),
    % First process type decs (must be done first), then
    % fn declarations (pre/postconds rely on sharing analysis which uses
    % types) and definitions
    (   % type equalities are asserted in teqdef/2 and used to
        % process other type defns to get canonical names for types
        member(teqdef(T,D), As),
        assert(teqdef(T, D)),
        fail
    ;   % source-level type defs are asserted in tdef/2   
        % (not ideal but it means we get renaming of type vars for
        % free).  Later we convert them to a reprentation suited to
        % sharing analysis (done on demand and asserted also)
        (   builtin_tdef(T, D)
        ;
            member(tdef(T0,D0), As),
            canon_tdef(tdef(T0,D0), tdef(T,D))
        ),
        assert(tdef(T, D)),
        % member(tdef(T1, _), TDs), % nondet
        % tdef_tdef_struct(TDs1, T1, type_struct_c(T1, S)),
        % assert(type_struct_c(T1, S)),
        fail
    ;
        % function declarations
        (   builtin_fdec((Fn :: ST))
        ;
            member((Fn :: ST), As)
        ),
        fdec_fdec_struct(Fn, ST, Fn1, T),
        assert(nfdec_struct(Fn1, T)),
        fail
    ;
        % function definitions - assert arity
        (   builtin_func_arity(Fn, Arity)
        ;
            member(fdef(FH, _), As),
            functor(FH, Fn, Arity)
        ),
        assert(func_arity(Fn, Arity)),
        update_max_cl_args(Arity),
        fail
    ;
        % function definitions
        member(fdef(PFH, PFB), As),
        ( PFB = extern ->
            assert(extern_fn(PFH))
        ; PFB = as_C(Str) ->
            name(AStr, Str),    % convert to retro-strings (char codes)
            name(AStr, Str1),
            assert(c_fn_def(PFH, Str1))
        ;
            retractall(var_number(_)),  % reset var numbers (optional)
            assert(var_number(0)),
            fdef_fdef_struct(PFH, PFB, FS), % type checking done here
            assert(FS)
        ),
        fail
    ;
        true
    ).  

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% external syntax -> abstract syntax
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% read file and return list of terms in abstract syntax
file_as(F, As) :-
    write('    Reading'(F)),
    flush_output,
    seen,
    % temporarily change precedence of ';'
    % (hopefully we don't abort before changing back)
    op(1010, xfy, (;)),
    see(F),
    read_header(_),
    in_as(As),
    nl,
    seen,
    % change precedence of ';' back to normal
    op(1100, xfy, (;)).

% read file until we get a blank line - current return value unused
% (XX in future we can return Pawns version number and various
% other meta-data; can also use #! line and scripts that depend on
% header)
read_header([version(141231)]) :-
    skip_to_blank_line(0'\n).

% skip until current char + next char are newlines, or EOF
skip_to_blank_line(Curr) :-
    get_code(C),
    ( (C == -1 ; C == 0'\n, Curr == 0'\n) ->
        true
    ;
        skip_to_blank_line(C)
    ).

% cvt current input to list of terms in abstract syntax
% we process type definitions first this so we know what data
% constructors there are then function declarations so we know
% what functions there are then function definitions.
% For modules we encapsulate reading an imported file and
% extracting the exported things (or at least those we want).  We
% read the file we are compiling, process the imports by reading those
% files and extracting a subset of the list of terms corresponding to
% (desired) exports and fudging definitions of exported type names and
% appending the lists of imported terms to the list of terms in the file
% to be compiled.
in_as(As) :-
    input_terms(Ts),
    split(is_import_def, Ts, TIDefs, Ts1),
    map(do_import, TIDefs, ITss), % this reads imported files
    split(is_export_def, Ts1, _TEDefs, Ts2),
    % XXX should check we are not exporting an import
    % elsewhere we check export_imp of
    % a mutable global and assert imported things
    % XXX should also assert exported things so non-exported things
    % can be declared static
    append([Ts2|ITss], Ts3),
    split(is_type_def, Ts3, TTDefs, TOs),
    split(is_fn_dec, TOs, TFDecs, TFDefs),
    map(es_as_type, TTDefs, ATDefs),
    % map(es_as_fdec, TFDecs, AFDecs),
    map(es_as_fdef, TFDefs, AFDefs),
    append(TFDecs, AFDefs, As1),
    append(ATDefs, As1, As).

% XX should be able to rename imports also ideally (problem with
% compilation to C - need to have unique names for exported things)
% Could munge names with file/module name prefix I guess.
do_import((import Ic from F), Ts) :-
    csv_list(Ic, Is),
    do_import1(F, just(Is), Ts).
do_import((import from F), Ts) :-
    do_import1(F, nothing, Ts).

% as above with maybe list of things to import
do_import1(F, MIs, Ts) :-
    name(F, FS),
    name('.pns', DPNS),
    append(FS, DPNS, FS1),
    name(F1, FS1),
    nl,
    write('    Importing'(F1)),
    flush_output,
    see(F1),
    input_imported(Ts, MIs),
    seen.
    
% read imported file from current input stream and
% return list of relevant terms (XXX should check all things declared
% exported are defined)
input_imported(Ts, MIs) :-
    input_terms(Ts1),
    split(is_export_def, Ts1, TEDefs, TOs),
    filter_map(to_export(TEDefs), TOs, Ts2),
    ( MIs = just(Is) ->
        filter(want_imported(Is), Ts2, Ts)
    ;
        Ts = Ts2
    ).

% XXX stub - should check fn/type name of T is member of Is
want_imported(Is, T) :-
    atom_of_input(T, A),
    member(A, Is).

% extract type/fn name from input term
atom_of_input((type C = _), A) :-
    functor(C, A, _).
atom_of_input((type C ---> _), A) :-
    functor(C, A, _).
atom_of_input((!C :: _), A) :-
    functor(C, A, _).
atom_of_input((C :: _), A) :-
    C \= (!_),
    functor(C, A, _).
atom_of_input((C = _), A) :-
    functor(C, A, _).
% atom_of_input((C : _), A) :- % old syntax
%     functor(C, A, _).

% checks if term is an export def
% XXX more sanity checking
is_import_def((import _ from _)).
is_import_def((import from _)).

% checks if term is an export def
% XXX more sanity checking
is_export_def((export_name _)).
is_export_def((export_imp _)).

% given list of export defs from a file we are importing and a term,
% return (possibly tweaked) term if it should be exported, otherwise fail
% we also assert imported here for type sigs (ugly)
to_export(EDs, (F :: T), (F :: T)) :-
    % type sigs of exported fns/global mutable vars are exported
    % for export_imp and export_name
    ( F = (!F1) ->
        true
    ;
        F1 = F
    ),
    member(ED, EDs),
    (   ED = (export_imp Ac),
        csv_list(Ac, As),
        member(F1, As),
        ( F1 = F ->
            assert(imported(F1))
        ;
            writeln('Error: export_imp of mutable global (ignored)'(F1)),
            fail
        )
    ;
        ED = (export_name Ac),
        csv_list(Ac, As),
        member(F1, As),
        assert(imported(F1))
    ),
    member(F1, As).
to_export(EDs, (L = R), FD) :-
    % fn defns are exported for export_imp only, for export_name we have
    % special "extern" definition (we need to know the arity if its used
    % in higher order code) XXX maybe we could have another way to do
    % this
    functor(L, F, _),
    ( member((export_imp Ac), EDs), csv_list(Ac, As), member(F, As) ->
        FD = (L = R)
    ; member((export_name Ac), EDs), csv_list(Ac, As), member(F, As) ->
        FD = (L = extern)
    ;
        fail
    ).
% to_export(EDs, (L: R), FD) :- % old syntax
%     % fn defns are exported for export_imp only, for export_name we have
%     % special "extern" definition (we need to know the arity if its used
%     % in higher order code) XXX maybe we could have another way to do
%     % this
%     functor(L, F, _),
%     ( member((export_imp Ac), EDs), csv_list(Ac, As), member(F, As) ->
%         FD = (L: R)
%     ; member((export_name Ac), EDs), csv_list(Ac, As), member(F, As)
%     ->
%         FD = (L: extern)
%     ;
%         fail
%     ).
to_export(EDs, (type L = R), TD) :-
    % type defns are exported in full for export_imp and abstract
    % versions are exported for export_name
    % XXX ??should import full version since pre/post conds of imported
    % functions might use data constructors.  Should allow this but just
    % ban use of data constructors from such types in importing file?
    % that way we do full sharing analysis using details of type.  Or
    % maybe if we export names of functions without type implementation
    % the pre/post conds should not use the data constructors - seems
    % reasonable?
    functor(L, F, _),
    ( member((export_imp Ac), EDs), csv_list(Ac, As), member(F, As) ->
        TD = (type L = R)
    ; member((export_name Ac), EDs), csv_list(Ac, As), member(F, As) ->
        % TD = (type L = R)
        % TD = (type L = abstract)
        % XXX hack for now
        name(F, FS),
        name('_absdc_', ABSDC),
        append(ABSDC, FS, FS1),
        name(F1, FS1),
        RHS =.. [F1, int],
        TD = (type L ---> RHS)
    ;
        fail
    ).
to_export(EDs, (type L ---> R), TD) :-
    % XXX see above
    functor(L, F, _),
    ( member((export_imp Ac), EDs), csv_list(Ac, As), member(F, As) ->
        TD = (type L ---> R)
    ; member((export_name Ac), EDs), csv_list(Ac, As), member(F, As) ->
        % TD = (type L = abstract)
        name(F, FS),
        name('_absdc_', ABSDC),
        append(ABSDC, FS, FS1),
        name(F1, FS1),
        RHS =.. [F1, int],
        TD = (type L ---> RHS)
    ;
        fail
    ).

% for imported things
:- dynamic(imported/1).

% checks if term is a type def
is_type_def((type _ = _)).
is_type_def((type _ ---> _)).

% checks if term is a fn dec
% XX fix if we tweek op priorities
is_fn_dec((_ :: _)).

% list of terms in input
input_terms(As) :-
    read(A),
    (A = end_of_file -> % XX catches var(X)
        As = []
    ;
        write('.'), % nl,
        flush_output,
        As = [A|As1],
        input_terms(As1)
    ).

% convert term as read from input (external prolog syntax) to internal
% representation (abstract syntax tree) - type stuff
% XX do more sanity checking
es_as_type((type TName = T), teqdef(TName, T)).
es_as_type((type TName ---> PTd), tdef(TName, CTs)) :-
    ( pctd_cts(PTd, CTs) ->
        true
    ;
        writeln('Error: malformed type definition:'((type TName ---> PTd))),
        TName = '_invalid',
        CTs = []
    ).

% convert term as read from input (external prolog syntax) to internal
% highish level representation - fn decs
% XX support fns/procs with no pre/postconds
% es_as_fdec(Fn :: ST, fdec(Fn, ST)).

% convert fn desc to lower level form (done after type definitions are
% processed)
% XX do more sanity checking
fdec_fdec_struct(Fn0, ST, Fn, I) :-
    ( canon_type_name(ST, T) ->
        I = T
    ;
        writeln('Error: malformed function type declaration:'(Fn0 :: T)),
        canon_type_name((void -> void
                    sharing f(v) = r pre nosharing post nosharing), I)
    ),
    ( Fn0 = (!Fn), atom(Fn) ->
        assert(mutable_global(Fn)),
        ( I = ref(_) ->
            true
        ;
            writeln('Error: mutable global must have ref type: '(Fn0 :: T))
        )
    ; atom(Fn0) ->
        Fn = Fn0
    ;
        writeln('Error: malformed declaration:'(Fn0 :: T)),
        Fn = '_foobar'
    ).

% store mutable globals, now called state variables
:- dynamic(mutable_global/1).

% convert term as read from input (external prolog syntax) to internal
% representation (abstract syntax tree) - fn defs
% XX do more sanity checking
es_as_fdef(T, fdef(PFH, PFB)) :-
    % old syntax
    % ((T = (PFH: PFB) ; T = (PFH = PFB)) -> % , pfdef_fdef(PFH, PFB, FH, FB) ->
    ( T = (PFH = PFB) -> % , pfdef_fdef(PFH, PFB, FH, FB) ->
        true
    ;
        writeln('ERROR: malformed input:'(T)),
        es_as_fdef(('_ignore'(v) = return), fdef(PFH, PFB))
    ).

% convert from src representation to core rep then to one used
% for sharing analysis (XX pick better name than fdef_struct)
% We check types and other things here
% XX more sanity/error checking, eg definedness
fdef_fdef_struct(PFH, PFB, FDS) :-
    % xxx(a),
    retractall(checking_pre_post),
    ( pfdef_fdef(PFH, PFB, FH, FB), fdef_fdef_struct1(FH, FB, FDS) ->
        functor(FH, _, Arity),
        update_max_cl_args(Arity)
    ;
    % XX can get here if arity of definition is too large
        writeln('ERROR: suspect definition:'(PFH = PFB)),
        fail
    ).

% as above without error trap
fdef_fdef_struct1(FH, FB, fdef_struct(FName, FAs, Stat)) :-
    FH =.. [FName|FHAs],
    writeln('    type analysis of '(FName)),
    map(arg_fdefarg, FHAs, FAs),
    nfdec_struct(FName, TF),
    % we replace distinct type vars with distinct new ground
    % types for checking (in the type we use variables so we
    % can get instances of the type for calls)
    smash_type_params(TF),
    length(FHAs, Arity),
    extract_ret_type(Arity, TF, TFArgs, TFR),
    % [TFR|TFArgs] is expected types [returnvar|FHAs]
    ( TF = arrow(_, _, _, _, _, _, _, _, ROIs, RWIs, WOIs) ->
        append(ROIs, RWIs, Is),
        globals_type_assoc(Is, VTm0)
    ;
        empty_assoc(VTm0)
    ),
    map_acc(flip_lookup_assoc, [returnvar|FHAs], TPs, VTm0, VTm1),
    % map(fst, TPs, [TFR|TFArgs]), % ignore purity Pty(for now)
    TPs = [TFR|TFArgs],
    % result type is not checked by add_typed_anns since it
    % doesn't know what is returned; its checked in add_last_anns
    % xxx(FName),
    add_typed_anns(FB, S1, VTm1, VTm),
    % check implict wo vars are instantiated and have types
    % compatible with declarations (like := type check)
    ( TF = arrow(_, _, _, _, _, _, _, _, _, _, WOIs) ->
        globals_type_assoc(WOIs, VTmWO),
        (   gen_assoc(WOV, VTmWO, WOTl), % generate & test
            ( get_assoc(WOV, VTm, WOTr) ->
                copy_term(WOTr, WOTrc),
                deannotate_type(WOTrc, WOTr1),
                % subsumes_chk is the name in older versions
                ( subsumes_chk(WOTr1, WOTl) ->
                    WOTr1 = WOTl,
                    % YY want nicer error message here
                    check_ho_types([], WOV='?', WOTl, WOTrc)
                ;
                    writeln('Error: "wo" parameter ill-typed: '(WOV,WOTl,WOTr))
                )
            ;
                writeln('Error: "wo" parameter not defined: '(WOV))
            ),
            fail
        ;
            true
        )
    ;
        true
    ),
    % append([WOIs, RWIs, FHAs], AllVs),
    % XXX should include ROIs?? but above seems to work ??
    % XXX must also include locally introduced state vars from called
    % fns with wo args; for now we over-approximate with all state vars
    % XXX NQR if we have a local var the same name as a state vars
    % (should warn about that at least).
    findall(SV, mutable_global(SV), AllVs),
    % need to include mutable args also!
    type_to_banged(TF, BVs),
    append(BVs, AllVs, AllVs1),
    sort(AllVs1, Vs1),
    % writeln(vs1(Vs1)),
    add_last_anns(S1, Stat, last(TFR), Vs1, _UVs, [], _IBVs),
    smash_type_vars(VTm).  % XX clobber any local type vars just in case...
    % writeq(Stat), nl.
    % XX should put list of type vars in fdef_struct?

% from type of defn, extract banged arguments. They are typically in the
% innermost arrow as the outer arrows just create closures (but not if a
% function is returned). We scan down through the arrows until we find a
% non-empty list of banged arguments and return them (otherwise return
% [])
type_to_banged(TF, BVs) :-
    ( TF = arrow(_, TF1, BVs1, _, _, _, _, _, _, _, _) ->
        ( BVs1 = [] ->
            type_to_banged(TF1, BVs)
        ;
            BVs = BVs1
        )
    ;
        BVs = []
    ).

% return global var/fn-type assoc for implicit args Is
globals_type_assoc(Is, VTm) :-
    empty_assoc(VTm0),
    globals_type_assoc_union(Is, VTm0, VTm).

% as above with initial VT map
globals_type_assoc_union(Is, VTm0, VTm) :-
    findall(V-T, (member(V, Is), nfdec_struct(V, T)), VTs),
    map0_acc(unpair_lookup_assoc, VTs, VTm0, VTm).

% call lookup_assoc given var-type pair
unpair_lookup_assoc(V-T, VTm0, VTm) :-
    lookup_assoc(V, VTm0, T, VTm).

% given type, strip off outer Arity arrows to give type of each arg and
% return type of fn
extract_ret_type(A, T0, TAs, T) :-
    (A = 0 ->
        TAs = [],
        T = T0
    ;
        T0 = arrow(TA, T1, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs),
        TAs = [TA|TAs1],
        A1 is A - 1,
        extract_ret_type(A1, T1, TAs1, T)
    ).

% given type, strip off outer Arity arrows to give type of each arg and
% return type of fn plus last arrow processed (the one wrapping the
% return type)
extract_ret_type_arrow(A, T0, TAs, T, OA) :-
    extract_ret_type_arrow1(A, T0, TAs, T, xyzzy, OA).

% as above with outer arrow passed in (at the top level its xyzzy and
% this should never be returned because arity should be at least 1)
extract_ret_type_arrow1(A, T0, TAs, T, OA0, OA) :-
    (A = 0 ->
        TAs = [],
        OA = OA0,
        T = T0
    ;
        T0 = arrow(TA, T1, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs),
        TAs = [TA|TAs1],
        A1 is A - 1,
        extract_ret_type_arrow1(A1, T1, TAs1, T, T0, OA)
    ).

% given type, strip off *all* Arity arrows to give type of each arg and
% return type of fn (also returns Arity)
extract_ret_type_max(A, T0, TAs, T) :-
    T0 = arrow(_, _, _, _, _, _, _, CLTs, _ROIs, _RWIs, _WOIs),
    extract_ret_type_max1(A, T0, TAs1, T),
    append(CLTs, TAs1, TAs).

% as above without extra closure args
extract_ret_type_max1(A, T0, TAs, T) :-
    ( T0 = arrow(TA, T1, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) -> % nonvar just in case
        extract_ret_type_max1(A1, T1, TAs1, T),
        TAs = [TA|TAs1],
        A is A1 + 1
    ;
        A = 0,
        TAs = [],
        T = T0
    ).

% count number of outer arrows in type
% type representation version
arrow_num(T, N) :-
    ( nonvar(T), T = arrow(_, T1, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) -> % nonvar just in case
        arrow_num(T1, N1),
        N is N1 + 1
    ;
        N = 0
    ).

arg_fdefarg(V, vp(V, vpe)).

% from arity + arrow type, get formal params from sharing declared,
% compute pre&post sharing sets (with paths of these vars)
% + list of DU (banged) vars + implicit args
% We need to traverse down Arity levels to get the right pre+post+BVs
% but generally we also have to traverse further to get the types of the
% formal params.  We can have Arity args supplied but expect extra args
% supplied later (and mentioned in pre/post; the types of these are in
% the nested arrow types in arg 2 of arrow/7) plus have some closure args
% supplied earlier (the types given explicitly in 4th-last arg of arrow/7),
% also used in pre/post.
arrow_to_sharing_dus(Arity, T0, [R|FAs], PreSS, PostSS, BVs, ROIs, RWIs, WOIs) :-
    % type params are replaced by distinct ground types in the same
    % way as we process function definitions, copy first to avoid
    % binding type vars where we shouldn't
    copy_term(T0, T),
    smash_type_params(T),
    % we get the (arrow) type nested Arity arrows down - that has
    % the sharing/DU + implicit arg info we need + type of result TR
    extract_ret_type_arrow(Arity, T, _, TR, OA),
    OA = arrow(_, _, BVs, _, _, Pre, Post, _, ROIs, RWIs, WOIs),
    % we repeat some work to get the formal res (R) + args (FAs) and
    % types of FAs (closure arg types CLATs and others TArgs)
    T = arrow(_, _, _, FAs, R, _, _, CLATs, _ROIs, _RWIs, _WOIs),
    length(FAs, NFA),
    length(CLATs, NCLA),
    NCFA is NFA - NCLA,
    extract_ret_type_arrow(NCFA, T, TArgs, _, _),
    % we look up types for all the implicit args;  ro+rw are treated as
    % args, wo is treated as result
    append(ROIs, RWIs, RIs),
    map(nfdec_struct, RIs, RITs),
    map(nfdec_struct, WOIs, WOTs),
    % RITs is types of implicit rw+ro args,
    % CLATs is the types of prev/outer args, TArgs is for rest
    append([RITs, CLATs, TArgs], AllArgTs),
    append(RIs, FAs, AllFAs),
    append([R|WOIs], AllFAs, AllResFAs),
    append([TR|WOTs], AllArgTs, AllResArgTs),
    empty_assoc(VTm0), % globals_type_assoc ???
    map_acc(flip_lookup_assoc, AllResFAs, TPs, VTm0, VTm1),
    % map(fst, TPs, AllResArgTs), % ignore purity Pty(for now)
    TPs = AllResArgTs,
    % add implicit self-sharing of args for pre
    map2(type_var_self_share, AllArgTs, AllFAs, SSelfs),
    append(SSelfs, SSS1),
    sort(SSS1, SSS2),
    cond_share(VTm1, Pre, SSS2, PreSS1),
    % we delete all share pairs involving anything but an arg var
    % or abstract
    filter_sharing_both_member(PreSS1, AllFAs, PreSS),
    % XXX
    % for postconditions we also add self-sharing for return var
    % which makes writing postconds more simple and declarative - return
    % var can be treated as being assigned at the start - but is less
    % precise - we can't have postcond which specifies only some paths
    % exist for return var.  Maybe have some compromise???  Eg, if we
    % allow dcons(x,y) = r syntax (shorthand for cases), maybe its not
    % so necessary to have this.  Perhaps we should just put up with
    % more verbose postconds for the sake of expressive power.
    type_var_self_share(TR, R, RSelfs),
    append(RSelfs, SSS2, SSS3),
    sort(SSS3, SSS4),
    % SSS4 = SSS2, % don't add self share for result
    cond_share(VTm1, Post, SSS4, PostSS1),
    % we delete all share pairs involving anything but an arg var,
    % the result var or abstract
    filter_sharing_both_member(PostSS1, [R|AllFAs], PostSS).

% given formal args for pre/post corresponding to closure args,
% compute list of cla(N) which they will be renamed to
cla_renaming([], _, []).
cla_renaming([_|FCLAs], N, [cla(N)|CLAs]) :-
    N1 is N + 1,
    cla_renaming(FCLAs, N1, CLAs).

% Currently use upper case (Prolog vars) for type vars and sometimes we
% want a ground type with at least one ref where there are vars (this is
% sufficient to check pre/post), so we smash type vars with ref(void).
% Generally we have multiple instances of the type for a fn and for each
% one we instantiate it further and process the pre/post for the
% instance.  YYY Could cache things more and/or avoid some recomputation in
% other ways.
smash_type_vars(T) :-
    ( var(T) ->
        T = ref(void)
    ; T = arrow(_, _, _, _, _, _, _, _, _, _, Is), var(Is) ->
        T = arrow(ref(void), ref(void), [], [], r, nosharing, nosharing, [], [], [], [])
    ;
        T =.. [_|As],
        map0(smash_type_vars, As)
    ).

% We replace (instantiate) distinct (type) vars with distinct terms of
% the form '_type_param'(N) where N is an integer.  This means they
% don't unify and can't be instantiated further in type checking.  For
% sharing analysis there is a single ref faked for these bogus types.
% We do this when we analyse a whole function.
smash_type_params(T) :-
    smash_type_params1(1, T, _).

% as above with number accumulator (arg order for foldl)
smash_type_params1(N0, T, N) :-
    ( var(T) ->
        T = '_type_param'(N0),
        N is N0 + 1
    ;
        T =.. [_|As],
        foldl(smash_type_params1, N0, As, N)
    ).

% convert from high level pre/postcondition to sharing set
% need some type info...
% we pass in self-sharing of args
cond_share(VTm0, PS, SS0, SS) :-
    ( PS = nosharing ->
        SS = SS0
    ;
        assert(checking_pre_post),
        pstat_stat(PS, S),
        add_typed_anns(S, S1, VTm0, _VTm),
        retractall(checking_pre_post),
        alias_stat(S1, SS0, SS)
    ).

% flag set when we do analysis of pre/post conditions to allow
% multiple defn of vars rather than give error msg
:- dynamic(checking_pre_post/0).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Some stuff for handling type definitions
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% XX
% XX we have a fake function called closure for pre/postconds only -
% handled specially for handling sharing of closure arguments
builtin_fdec((!io :: ref(void))).
builtin_fdec((closure :: _A -> _B sharing f(a)=b pre nosharing post
nosharing)).
builtin_fdec((not :: bool -> bool)).
builtin_fdec((and :: bool -> bool -> bool)).    % strict
builtin_fdec((or :: bool -> bool -> bool)).     % strict
builtin_fdec((< :: int -> int -> bool)).
builtin_fdec((> :: int -> int -> bool)).
builtin_fdec((<= :: int -> int -> bool)).
builtin_fdec((leq :: int -> int -> bool)). % XXX
builtin_fdec((eq :: int -> int -> bool)).
% delete and rename fn in io.pns ?
% builtin_fdec((print_int :: int -> void implicit rw io)).
builtin_fdec((>= :: int -> int -> bool)).
builtin_fdec((+ :: int -> int -> int)).
builtin_fdec((- :: int -> int -> int)).
builtin_fdec((* :: int -> int -> int)).
builtin_fdec((div :: int -> int -> int)).
builtin_fdec((mod :: int -> int -> int)).
% XXX what do we do about equality? Pass type representations around when we
% compile?  Implement type classes properly? Fake it for now...
builtin_fdec((== :: T -> T -> bool sharing eq(x,y)=b pre x=y post nosharing)).
builtin_fdec((apply :: (A -> B) -> A -> B)). % XXX implicit, sharing NQR

% XX
builtin_func_arity(closure, 999999999). % XX should be enough
builtin_func_arity(not, 1).
builtin_func_arity(and, 2).
builtin_func_arity(or, 2).
builtin_func_arity(<, 2).
builtin_func_arity(>, 2).
builtin_func_arity(<=, 2).
builtin_func_arity(leq, 2). % XXX
builtin_func_arity(eq, 2). % XXX
% builtin_func_arity(print_int, 1).
builtin_func_arity(>=, 2).
builtin_func_arity(+, 2).
builtin_func_arity(-, 2).
builtin_func_arity(*, 2).
builtin_func_arity(div, 2).
builtin_func_arity(mod, 2).
builtin_func_arity(==, 2).
builtin_func_arity(apply, 2).

% XX
builtin_tdef(void, [dcons(void, [])]).
builtin_tdef(int, [dcons(xyzzy, [])]).
builtin_tdef(bool, [dcons(false, []), dcons(true, [])]).
builtin_tdef(ref(T), [dcons('_ref', [T])]).
builtin_tdef(list(T), [dcons(nil, []), dcons(cons, [T, list(T)])]).
builtin_tdef(maybe(T), [dcons(nothing, []), dcons(just, [T])]).
builtin_tdef(pair(T1,T2), [dcons(t2, [T1, T2])]). % XX tuple naming?
builtin_tdef('_type_param'(_T), [dcons('_typeparam', [void])]).
% we have a _closure type for runtime representation of closures
% XXX add enough cases here (or assert separately) for max_cl_args
% or allow general case and/or optimise some cases
% XXX constant added temporarily to avoid adtpp/gcc bug
builtin_tdef('_closure', [
    dcons('_cl_delete_this_when_adtpp_fixed',[]),
    dcons('_cl0',[arrow(T,T,[],[],r,N,N,[],[],[],[]), int]),
    dcons('_cl1',[arrow(T,T,[],[],r,N,N,[],[],[],[]), int, ref(void)]),
    dcons('_cl2',[arrow(T,T,[],[],r,N,N,[],[],[],[]), int, ref(void), ref(void)]),
    dcons('_cl3',[arrow(T,T,[],[],r,N,N,[],[],[],[]), int, ref(void), ref(void), ref(void)]),
    dcons('_cl4',[arrow(int,int,[],r,N,N,[],[],[],[],[]), int, ref(void), ref(void), ref(void), ref(void)])
        ]) :- N = nosharing.

% data constructors - some built in (should include those above),
% some asserted from type defns etc XX
data_cons(D) :-
    prog_dcons(D). % asserted
data_cons(void).
data_cons(N) :- number(N). % XX hack
data_cons(true).
data_cons(false).
data_cons(nil).
data_cons(cons(_,_)).
data_cons(nothing).
data_cons(just(_)).
data_cons(t2(_,_)).
data_cons('_typeparam'(_)). % not needed?
data_cons('_cl0'(_,_)).
data_cons('_cl1'(_,_,_)).
data_cons('_cl2'(_,_,_,_)).
data_cons('_cl3'(_,_,_,_,_)).
data_cons('_cl4'(_,_,_,_,_,_)). % XXX add more
data_cons(pair(_,_)).
% data_cons(array_(_)). % XX hack for sharing analysis

% disjunction of data constructors with types as arg ->
% list of abstract versions
% We use dcons for type constructors - could use a separate
% representation
pctd_cts(PCTd, CTs) :-
    (PCTd = (PCT1; PCTd1) ->
        assert_new_dcons(PCT1),
        PCT1 =.. [C|Ts],
        CTs = [dcons(C, Ts) | CTs1],
        pctd_cts(PCTd1, CTs1)
    ;
        assert_new_dcons(PCTd),
        PCTd =.. [C|Ts],
        CTs = [dcons(C, Ts)]
    ).

% XX should have list passed around; should keep type here also
assert_new_dcons(DC) :-
    functor(DC, F, N),
    functor(DC1, F, N),
    assert(prog_dcons(DC1)).

:- dynamic(prog_dcons/1).

% XX
% type equalities
:- dynamic(teqdef/2).

% XX
% discriminated union types
:- dynamic(tdef/2).

% expand/use type equality defns to get canonical names in tdef
canon_tdef(tdef(T, CTs), tdef(T, CTs1)) :-
    map(canon_ct, CTs, CTs1).

% as above for single constructor in tdef
canon_ct(dcons(C, Ts), dcons(C, Ts1)) :-
    map(canon_type_name, Ts, Ts1).

% expand/use type equality defns to get canonical name for type
% eg if we have type bools = list(bool) and we are given bools
% we return list(bool).  Also transform arrows - this is the main
% complication.
% XX Nasty because type vars are Prolog vars for now
% XXX should check for cyclic type equalities (will cause loop)
% XX and LHS should not have nested expression
% For arrows, typically we have something like
% t1 -> t2 -> t3 sharing f(x1,x2)=x3 pre s post f
% The sharing info above is associated with the innermost arrow (thats
% typically when the function is actually executed, rather than creating
% a closure).  However, the inner application doesn't have a type for x1
% - this needs to be inferred (as t1) from the outer context.  Also,
% there is no explicit sharing declared for the outer arrow - we infer
% that x1 is shared by the closure argument of the resulting function as
% the postcondition; the precondition is the same as the inner one.
% So we push the types of the outer arrows into the inner ones, and
% push inner preconditions to the outer arrows and add the closure
% postconditions.  The formal params are also inherited outwards.  We
% end up some formal params which are unused, eg for the outer arrow
% we get t1 -> (...) sharing f(x1,x2)=x3 pre s post f', where x2 is
% never actually given a value. We could remove x2 from the param list,
% and also from the percondition (where it may occur) but thats rather
% tricky.  It turns out that the extra params do no harm and are
% basically ignored later.  In the low level repersentation, types of
% closure arguments are given explicitly so there is no ambiguity (if
% the src code had t1 -> (...) sharing f(x1,x2)=x3 it would look like x1
% is a closure argument.
%
% We also handle implicit parameters. ro and rw parameters are inherited
% to outer (more left) arrows whereas wo parameters are just added at
% the level they are declared.
% XX should allow multiple (nested) implicit argument declarations with
% sensible defaults for inheriting - may not be done ideally
canon_type_name(ST, T) :-
    ( ctn1([], ST, T) ->
        true
    ;
        writeln('Error: dodgey type name:'(ST)),
        T = ref(void) % carry on with default type
    ).

% as above with list of types from outer arrows
ctn1(Ts, ST, T) :-
    ( var(ST) ->
        T = ST
    ; ( ST = (STL -> SR),
        nonvar(SR),
        SR = (STR sharing L = R pre Pre post Post)
      )
    ->
        % we have hit some explicit sharing info - deal with it + use
        % the outer types Ts passed in
        ctn1([], STL, TL),
        append(Ts, [TL], Ts1),
        ctn1(Ts1, STR, TR),
        ( nonvar(TR), TR = implicit(TR1, ROIs, RWIs, WOIs) ->
            true
        ;
            TR1 = TR,
            ROIs = [],
            RWIs = [],
            WOIs = []
        ),
        L =.. [_Fn|LAs],
        get_bang_args(LAs, BVs, LAs1),
        T = arrow(TL, TR1, BVs, LAs1, R, Pre, Post, Ts, ROIs, RWIs, WOIs)
    ; ST = (STL -> STR), nonvar(STR), STR = (_ -> _) ->
        % arrow with RHS an arrow - need to recursively process RHS
        % and from the result infer the sharing for this arrow
        ctn1([], STL, TL),
        append(Ts, [TL], Ts1),
        ctn1(Ts1, STR, TR),
        TR = arrow(_, _, _RBVs, RLAs, RR, RPre, _, _, ROIs, RWIs, _),
        % we say no vars are banged since we just create a closure
        length(Ts, NTs),
        NCLAs is NTs + 1,
        take(NCLAs, RLAs, CLAs),
        CL =.. [closure|CLAs],
        % T = arrow(TL, TR, [], CLAs, RR, RPre, RR = CL, Ts, _ROIs,
        % _RWIs, _WOIs)
        T = arrow(TL, TR, [], RLAs, RR, RPre, RR = CL, Ts, ROIs, RWIs, [])
    ; ST = (STL -> STR) ->
        % no sharing specified - assume abstract sharing
        % All args x should have x=abstract in pre and in post we want
        % result r=abstract plus any components of r which can share with a
        % component of arg x.  Currently have x=abstract in post always;
        % doesn't lose precision since we project pre+post onto r.
        ctn1([], STL, TL),
        ctn1(Ts, STR, TR),
        length(Ts, NTs),
        NTs1 is NTs + 1,
        take(NTs1, [a1,a2,a3,a4,a5,a6,a7,a8,a9,a10,a11,a12,a13], LAs), % XXX
        vars_abs_eq(LAs, Pre),
        vars_abs_eq([r|LAs], Post),
        ( nonvar(TR), TR = implicit(TR1, ROIs, RWIs, WOIs) ->
            true
        ;
            TR1 = TR,
            ROIs = [],
            RWIs = [],
            WOIs = []
        ),
        T = arrow(TL, TR1, [], LAs, r, Pre, Post, Ts, ROIs, RWIs, WOIs)
    ; ST = (ST1 implicit Ic) ->
        ctn1(Ts, ST1, ST2),
        gather_implicits(Ic, ROIs, RWIs, WOIs),
        T = implicit(ST2, ROIs, RWIs, WOIs)
    ; teqdef(ST, ST1) ->
        ctn1([], ST1, T)
    ;
        % top level type constructor is canonical
        ST =.. [F|As0],
        map(ctn1([]), As0, As),  % get canon version of args
        T =.. [F|As]
    ).

% scan through comma-separated sequence of implicit parameters
% declared and return sorted lists of ro, rw, wo implicit params
gather_implicits(Ic, ROIs, RWIs, WOIs) :-
    ( gather_imps(Ic, ROIs0, RWIs0, WOIs0) ->
        % XXX should check ROIs0, RWIs0, WOIs0 don't intersect
        sort(ROIs0, ROIs),
        sort(RWIs0, RWIs),
        sort(WOIs0, WOIs)
    ;
        writeln('Error in implicit parameter declarations:'(Ic))
    ).

% as above, returning unsorted lists
gather_imps((ro P), [P], [], []) :-
    atom(P).
gather_imps((rw P), [], [P], []) :-
    atom(P).
gather_imps((wo P), [], [], [P]) :-
    atom(P).
gather_imps((Ic1, Ic2), ROIs, RWIs, WOIs) :-
    gather_imps(Ic1, ROIs1, RWIs1, WOIs1),
    gather_imps(Ic2, ROIs2, RWIs2, WOIs2),
    append(ROIs1, ROIs2, ROIs),
    append(RWIs1, RWIs2, RWIs),
    append(WOIs1, WOIs2, WOIs).

% take non-empty list of vars eg [v1,v2] and return v1=abstract;...
vars_abs_eq([V], (V = abstract)).
vars_abs_eq([V|Vs], (V = abstract; Es)) :-
    vars_abs_eq(Vs, Es).

% from list of possibly banged vars, extract banged vars and vars
% allow/ignore type annotations
get_bang_args([], [], []).
get_bang_args([LA|LAs0], BVs, LAs) :-
    ( (LA = (!V) ; LA = (!V::_)), atom(V) ->
        BVs = [V|BVs1],
        LAs = [V|LAs1]
    ; (LA = V ; LA = (V::_)), atom(V) ->
        BVs = BVs1,
        LAs = [V|LAs1]
    ;
        writeln('ERROR: malformed argument in sharing (ignored):'(LA)),
        BVs = BVs1,
        LAs = LAs1
    ),
    get_bang_args(LAs0, BVs1, LAs1).

% get type annotation from closure arg of sharing description
get_type_annotation((_::T), T).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% function definition -> abstract syntax
% XXX should do more sanity checking
pfdef_fdef(CFH, CFB, FH, FB) :-
    FH = CFH,
    % pstat_stat(CFB, FB), writeln(CFB), nl, writeq(FB), nl.
    ( pstat_stat(CFB, FB) ->
        true
    ;
        writeln('ERROR: dodgey definition:'(CFH = CFB))
    ).

% statement -> abstract core syntax
% Nested expressions etc are flattened to get a bunch of statements for
% each simple src statement.  Indirect !annotations (those at the end of
% the statement) are added to each statement
% in the bunch. eg *!x := foo([])!y is changed to something like
% v123 = [] !y; v456 = foo(v123) !y; *!x := v456 !y
% The way annotations are handled is we have a list of annotations for
% each basic statement.  For mutability (as above) we use bang(i, V) for
% indirect and bang(d, V) direct (LHS of := and args of apps).  For
% ! on applications (indicating implicit args) we use app_bang(Fn).
% Also add src(orig_stat) when we expand things.
% Later passes add more annotations to keep track of type information,
% liveness, etc which keep the statements themselves the same.
pstat_stat(PS, S) :-
    ( var(PS) ->
        % XX something major is wrong 
        writeln('ERROR: Prolog var encountered'),
        PS = foobar,
        pstat_stat(PS, S)
    ; PS = (if C then A else B) ->
        pstat_stat((cases C of {case true: A case false: B}), S)
    ; PS = (if C then A) ->
        pstat_stat((if C then A else void), S)
    ; PS = {PS1} ->
        pstat_stat(PS1, S)
    ; PS = (PS1 ; PS2) ->
        pstat_stat(PS1, S1),
        pstat_stat(PS2, S2),
        S = seq(S1, S2)-[]
    % XXXX explicit type info better attached to RHS, eg
    % *tp = (mt :: bst(int)) (done, need to clean up old stuff)
    % With explicit types, add extra of_type(bst(int)) annotation and in
    % type analysis check inferred type is an instance.  Could allow for
    % var = var only, or add extra eqns and only check for annotation
    % for such eqns to simplify code.  Process in add_typed_anns_veq?
    ; PS = (PS1 :: T) -> % XX rethink explicit type decs?
        canon_type_name(T, T1),
        ( atom(PS1), \+ data_cons(PS1) ->
            V = PS1,
            Ann = [src(PS), typed(T1), decl_only(V)]
        ; PS1 = (!V), atom(V), \+ data_cons(V) ->
            Ann = [src(PS), typed(T1), decl_only(V), bang(d, V)]
        ;
            writeln('Error: illegal statement'(PS1 :: T)),
            V = '_dummy',
            Ann = [src(PS)]
        ),
        S = var_stat(V)-Ann
    ; PS = (PE1 := PE2) ->
        % want *!v1 := v2
        to_star_bang_var(PE1, V1, ES1),
        to_var(PE2, V2, ES2),
        foldr(combine_stats,
            assign(V1, V2)-[src(PS)],
            [ES1, ES2], S1),
        propogate_anns(S1, S)
    ; PS = (PE1 = PE2) ->
        pstat_eq_stat(PE1, PE2, S)
    ; PS = (PS1 ! V) ->
        pstat_stat(PS1, S1),
        S1 = C1-Anns1,
        ( atom(V) ->
            S2 = C1-[src(PS), bang(i, V)|Anns1]
        ;
            write('ERROR: nonvar after ! (ignored):'(PS1 ! V)),
            nl,
            S2 = S1,
            C1 = [src(PS)]
        ),
        propogate_anns(S2, S)
    ; PS = (cases PE of PCd) ->
        % XXX currently we allow target of case to have !var in
        % expression but not extra !var at end.  We could allow
        % this but it means we have to handle infix ! for expressions
        % (and maybe fix operator precedence etc).  For now the user
        % has to use a separate equation with infix ! before the case.
        to_var(PE, V, ES),
        propogate_anns(ES, ES1),
        pcases_cases(PCd, Cs),
        combine_stats(ES1, cases(V, Cs)-[], S)
% XXX should we get rid of explicit return in src language???
% ignore for now
    ; PS = return(PE1) ->
        pstat_stat(PE1, S)
    ; PS = return ->
        pstat_stat(void, S)
    ; % var or procedure call
        to_var(PS, V, ES),
        combine_stats(ES, var_stat(V)-[src(PS)], S1),
        propogate_anns(S1, S)
    ).

% cases for equality
% hmm: repeats code from to_var etc:-(
% could avoid but it would introduce more v=v1?
% maybe thats not too much of a problem??
% XXX nice to support dcons(x,y) = rhs - map to
% newvar = rhs; cases newvar ( case dcons(x,y): ...); need to handle
% liveness etc some time
pstat_eq_stat(PEl, PEr, S) :-
    ( var(PEl) ->
        % XX something major is wrong 
        writeln('ERROR: Prolog var encountered - aborting'),
        fail
    ; PEl = (**PE1) ->
        pstat_eq_stat(*(*PE1), PEr, ST3-Anns3),
        % could remove src() from Anns3
        propogate_anns(ST3-[src(PEl = PEr)|Anns3], S)
    ; PEl = (***PE1) ->
        pstat_eq_stat(*(*(*PE1)), PEr, ST3-Anns3),
        % could remove src() from Anns3
        propogate_anns(ST3-[src(PEl = PEr)|Anns3], S)
    ; PEl = (*(*PE1)) ->
        % * * x = r -> *v=r; *x=v
        fresh_var(V),
        pstat_eq_stat(*V, PEr, S1),
        pstat_eq_stat(*PE1, V, S2),
        combine_stats(S1, S2, ST3-Anns3),
        % could remove src() from Anns3
        propogate_anns(ST3-[src(PEl = PEr)|Anns3], S)
    ; PEl = (*PE1) ->
        % want *v1 = v2
        to_var(PEr, V2, ES2),
        ( PE1 = !V1, atomic(V1), \+ data_cons(V1) ->
            combine_stats(ES2, deref_eq(V1, V2)-[src(PEl=PEr), bang(d, V1)], S)
        ; PE1 = V1, atomic(V1), \+ data_cons(V1) ->
            combine_stats(ES2, deref_eq(V1, V2)-[src(PEl=PEr)], S)
        ;
            writeln('Error: illegal statement'(PEl = PEr)),
            S = empty_stat-[src(PEl=PEr)]
        )
    ; 
        % if LHS is not * it should be a var
        % or !var (for init of mutable vars)
        % XXX if we don't insist on mutvars being declared with !
        % then ! on LHS of = should be an error
        % (XXX could also allow type annotations here)
        (   (   atom(PEl), Vl = PEl, Anns = [src(PEl=PEr)]
            ;
                PEl = (!Vl), atom(Vl), Anns = [src(PEl=PEr), bang(d, Vl)]
            )
        ->
            ( data_cons(Vl) ->
                writeln('ERROR: constant on LHS of equation:'(Vl))
            ;
                true
            ),
            ( var(PEr) ->
                % XX something major is wrong 
                writeln('ERROR: Prolog var encountered - aborting'),
                fail
            ; PEr = (PE1::T) ->
                canon_type_name(T, T1),
                to_var(PE1, V2, ES2),
                combine_stats(ES2, eq_var(Vl, V2)-[src(PEl= (PE1::T)), typed(T1)], S)
            ; PEr = (*PE2) ->
                % want v1 = *v2
                to_var(PE2, V2, ES2),
                combine_stats(ES2, eq_deref(Vl, V2)-Anns, S)
            ; PEr = (**PE2) ->
                to_var(*PE2, V2, ES2),
                combine_stats(ES2, eq_deref(Vl, V2)-Anns, S)
            ; PEr = (***PE2) ->
                to_var(*(*PE2), V2, ES2),
                combine_stats(ES2, eq_deref(Vl, V2)-Anns, S)
            ; data_cons(PEr) -> % should pass env
                % XXX should check for incorrect arity?
                % cons(h,t) -> cons(hv,tv)
                PEr =.. [F|PEs],
                length(PEs, Arity),
                map2(to_var, PEs, Vs, ESs),
                foldr(combine_stats,
                    eq_dc(Vl, F, Arity, Vs)-Anns,
                    ESs, S)
            ; PEr = (!PEr1) ->
                % more repeated code - getting bad!
                ( functor(PEr1, F, Arity), func_arity(F, DecArity) ->
                    % f(h,t) -> v = f(hv,tv)
                    PEr1 =.. [F|PEs],
                    map2(to_var, PEs, Vs, ESs),
                    ( Arity = DecArity ->
                        foldr(combine_stats,
                            eq_sapp(Vl, F, Vs)-[app_bang(F)|Anns],
                            ESs, S)
                    ; Arity < DecArity ->
                        foldr(combine_stats,
                            eq_papp(Vl, F, Vs)-[app_bang(F)|Anns],
                            ESs, S)
                    ;
                        % XX trf to eq_sapp(new, ...); eq_sapp(Vl, % new,...)
                        writeln('Hyper-saturated applications not yet supported'),
                        fail
                    )
                ; atom(PEr1) ->
                    % XXX could count this as an error?
                    S = eq_var(Vl, PEr1)-[bang(d, PEr1)|Anns]
                ;
                    writeln('Error: ! prefixing non-var/application :'(PEr)),
                    S = eq_var(Vl, '_err')-Anns
                )
            ; functor(PEr, F, Arity), func_arity(F, DecArity) ->
                % f(h,t) -> v = f(hv,tv)
                PEr =.. [F|PEs],
                map2(to_var, PEs, Vs, ESs),
                ( Arity = DecArity ->
                    foldr(combine_stats,
                        eq_sapp(Vl, F, Vs)-Anns,
                        ESs, S)
                ; Arity < DecArity ->
                    foldr(combine_stats,
                        eq_papp(Vl, F, Vs)-Anns,
                        ESs, S)
                ;
                    % XX trf to eq_sapp(new, ...); eq_sapp(Vl, %
                    % new,...)
                    writeln('Hyper-saturated applications not yet supported'),
                    fail
                )
            % currently we must check this after functions calls since
            % "function calls" may have not arguments but the conversion
            % to (partial) applications resolves naming; we don't
            % currently pass in a proper var-type map for functions XXX
            ; atom(PEr) ->
                S = eq_var(Vl, PEr)-Anns
            ; % XXX more sanity checking
                % Application of variable to args
                PEr =.. [F|PEs],
                map2(to_var, PEs, Vs, ESs),
                foldr(combine_stats,
                    eq_app(Vl, F, Vs)-Anns, ESs, S)
            )
        ;
            write('ERROR: illegal LHS:'(PEl = PEr)),
            nl,
            S = empty_stat-[]
        )
    ).

% convert expression to var plus extra stat(s)
% XXXX add processing of type annotations
% XXX add processing of && and || (generate case statement - hopefully
% gcc -O3 is up to the challenge!)
to_var(PE, V, ES) :-
    % data_cons case needs to be before atom case
    ( var(PE) ->
        % XX something major is wrong 
        writeln('ERROR: Prolog var encountered'),
        PE = foobar,
        to_var(PE, V, ES)
    ; PE = (PE1 :: T) ->
        canon_type_name(T, T1),
        fresh_var(V),
        to_var(PE1, V1, ES1),
        combine_stats(ES1, eq_var(V, V1)-[typed(T1)], ES)
    ; data_cons(PE) -> % should pass env
        % cons(h,t) -> v + v = cons(hv,tv)
        fresh_var(V),
        PE =.. [F|PEs],
        length(PEs, Arity),
        map2(to_var, PEs, Vs, ESs),
        foldr(combine_stats,
            eq_dc(V, F, Arity, Vs)-[],
            ESs, ES)
    % need to put * before defined functions otherwise indirection gets
    % treated as a partial application to multiplication (if we want the
    % latter we have to have another multiply fn)
    ; PE = (*PE1) ->
        % *e -> v + v = *ev
        fresh_var(V),
        to_var(PE1, V1, ES1),
        combine_stats(ES1, eq_deref(V, V1)-[], ES)
    ; functor(PE, F, Arity), func_arity(F, DecArity) ->
        % f(h,t) -> v + v = f(hv,tv)
        fresh_var(V),
        PE =.. [F|PEs],
        map2(to_var, PEs, Vs, ESs),
        ( Arity = DecArity ->
            foldr(combine_stats,
                eq_sapp(V, F, Vs)-[],
                ESs, ES)
        ; Arity < DecArity ->
            foldr(combine_stats,
                eq_papp(V, F, Vs)-[],
                ESs, ES)
        ;
            % XX trf to eq_sapp(new, ...); eq_sapp(PEl, % new,...)
            writeln('Hyper-saturated applications not yet supported'),
            fail
        )
    ; atom(PE) ->   % already have a var - nothing to do
        V = PE,
        ES = empty_stat-[]
%     ; PE = (PE1 ! PV) ->    % XX not needed - handled in stats?
%         to_var(PE1, V, ES1),
%         add_anns(ES1, [bang(PV)], ES)
    ; PE = (!PE1) ->
        ( atom(PE1) ->
            ( func_arity(PE1, _DecArity) ->
                to_var(PE1, V, ES1),
                combine_stats(empty_stat-[app_bang(PE1)], ES1, ES)
            ;
                V = PE1,
                ES = empty_stat-[bang(d, V)]
            )
        ; PE1 =.. [PE1F, _|_] ->
            to_var(PE1, V, ES1),
            combine_stats(empty_stat-[app_bang(PE1F)], ES1, ES)
        ;
            writeln('Error: ! prefixing non-var/application (ignored):'(!PE1)),
            to_var(PE1, V, ES)
        )
    ; % XXX more sanity checking
        % Application of variable to args
        fresh_var(V),
        PE =.. [F|PEs],
        map2(to_var, PEs, Vs, ESs),
        foldr(combine_stats,
            eq_app(V, F, Vs)-[], ESs, ES)
    ).

% convert expression to *!var (LHS of :=) plus extra stat(s)
to_star_bang_var(PE, V, ES) :-
    ( var(PE) ->
        % XX something major is wrong 
        writeln('ERROR: Prolog var encountered'),
        PE = foobar,
        to_star_bang_var(PE, V, ES)
    ; atom(PE) ->
        write('Error: need *! on LHS of := (added):'(PE)),
        nl,
        V = PE,
        ES = empty_stat-[bang(d, V)]
    ; PE = (!PE1) ->
        ( atom(PE1) ->
            write('Error: need * on LHS of := (added):'(PE)),
            nl,
            V = PE1,
            ES = empty_stat-[bang(d, V)]
        ;
            write('Error: ! prefixing nonvar (ignored):'(PE)),
            nl,
            to_star_bang_var(PE1, V, ES)
        )
    ; PE = (*PE1) ->
        % *e -> v + v = *ev
        to_var(PE1, V, ES)
    ; data_cons(PE) -> % should pass env
        write('ERROR: data constructor on LHS of := (ignored)'(PE)),
        nl,
        fresh_var(V),
        ES = empty_stat-[]
    ; % functor(PE, F, N), N > 0 ->
        write('Error: function call as LHS of := (ignored)'(PE)),
        nl,
        fresh_var(V),
        ES = empty_stat-[]
    ).

% add annotations to (each stat in sequence of) stat(s)
% eg, if we have v = f(g(!x,y),!z) !u, will flatten RHS then use
% this to add !u to each of the equations
add_anns_last(S0, Anns, S) :-
    (S0 = seq(SA0, SB0)-AnnsT ->
        SB0 = CB-Anns0,
        append(Anns, Anns0, Anns1),
        SB = CB-Anns1,
        S = seq(SA0, SB)-AnnsT
    ;
        S0 = C0-Anns0,
        append(Anns, Anns0, Anns1),
        S = C0-Anns1
    ).

% Propogate annotations from outer seq etc to all inner stats (= etc)
propogate_anns(S0, S) :-
    S0 = _-Anns0,
    prop_anns(S0, Anns0, S).

% As above given Anns from top level
prop_anns(S0, Anns, S) :-
    (S0 = seq(SA0, SB0)-_ ->
        prop_anns(SA0, Anns, SA),
        prop_anns(SB0, Anns, SB),
        S = seq(SA, SB)-Anns
    ;
        S0 = C0-_,
        S = C0-Anns
    ).

% combine two stats into a sequence (avoid extra empty_stat)
% Anns are combined for seq only; propogated to all stats in a later pass
combine_stats(S1, S2, C-Anns) :-
    S1 = C1-Anns1,
    S2 = C2-Anns2,
    % ord_union(Anns2, Anns1, Anns),  % YY better?
    append(Anns2, Anns1, Anns),
    ( C1 = empty_stat ->
        C = C2
    ; C2 = empty_stat ->
        C = C1
    ;
        C = seq(S1, S2)
    ).

% cases -> abstract syntax
% syntax tricky XX
pcases_cases({CPCd}, Cs) :-
    pcases_cases(CPCd, Cs).
pcases_cases((case PCd), Cs) :-
    pcases_cases1(PCd, Cs).

pcases_cases1(PCd, Cs) :-
    (PCd = (PC1 case PCd1) ->
        pcase_case(PC1, C1),
        Cs = [C1 | Cs1],
        pcases_cases1(PCd1, Cs1)
    ;
        pcase_case(PCd, C),
        Cs = [C]
    ).

% case -> abstract syntax
% we convert normal patterns to deref patterns to make core language
% simpler (may not be best for efficient compilation) which may result
% in extra = statements
pcase_case((PE: PS), C) :-
    % allow 'default' keyword for patterns
    (PE = default ->
        pstat_stat(PS, S),
        C = case_def(S)
    ; data_cons(PE), PE =.. [F|PEs], pat_args_ok(PEs) -> % should pass env
        length(PEs, Arity),
        map_acc(pat_arg, PEs, PAs, [], ESs),
        pstat_stat(PS, S1),
        foldr(combine_stats, S1, ESs, S),
        C = case_dc(F, Arity, PAs, S)
    ;
        write('ERROR: ill-formed pattern (made default):'(PE)),
        nl,
        % XX arbitrary fall-back (may break some things)
        pstat_stat(PS, S),
        C = case_def(S)
    ).

% check each pattern arg is a distinct var or deref of a var
% (may fail)
pat_args_ok(PEs) :-
    map(var_or_deref_var, PEs, Vs),
    length(Vs, A),
    sort(Vs, UVs), % removes duplicates
    length(UVs, A).

% check for var or *var
% (may fail)
var_or_deref_var(E, V) :-
    ( atom(E) ->
        V = E
    ;
        E = (*E1),
        atom(E1),
        V = E1
    ).

% process a pattern arg.  If its not a deref make it one + add equation.
pat_arg(E, DV, ESs0, ESs) :-
    ( E = (*DV) ->
        ESs = ESs0
    ; % atom(E)
        fresh_var(DV),
        ESs = [eq_deref(E, DV)-[]|ESs0]
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% definition/use/liveness analysis
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% take stat with annotations plus vars defined so far, return same stat with
% extra definition-related annotations + new var list
% We want to
% 1) check vars are defined before they are used
% 2) know where to introduce vars in the compiled code (could introduce
% them at at the top level of a function but better is in nested blocks
% but if a var is defined in several branches of a case its definition
% may need to be lifted outside XXX skip this for now)
% XXX in fact skip all of this for now - not needed for sharing
% XXX should add annotation to say where var should be introduced by
% compiler and separate this from = code; for cases, figure out which
% vars are introduced in multiple branches and add the annotation to the
% cases statement.

% Add last_stat, used_later(vars), last_use(v) annotations so we put return
% statements in the compiled code, etc and avoid
% mutability errors for dead vars (XX probably don't need these annotations
% on all the stats we put them on)
% We do bottom to top traversal with current list of used vars (should
% be initialised to parameters) + last statement flag
% The expected return type is passed in with the last statement flag and
% its checked here.
add_last_anns(C0-Ann0, C-Ann, LSF, UVs0, UVs, IBVs0, IBVs) :-
    C0 = seq(Sa0, Sb0),
    add_last_anns(Sb0, Sb, LSF, UVs0, UVs1, IBVs0, IBVs1),  % traverse in reverse
    add_last_anns(Sa0, Sa, not_last, UVs1, UVs, IBVs1, IBVs),
    C = seq(Sa, Sb),
    Ann = Ann0.
add_last_anns(C0-Ann0, C-Ann, LSF, UVs0, UVs, IBVs0, IBVs) :-
    % XX Could print warning (somewhere) when Vl is a last occurrence and
    % there is no effect (eg, not eq_sapp or eq_app)
    (
        (
            C0 = eq_dc(_, _, _, Args)
        ;
            C0 = eq_sapp(_, _, Args)
        ;
            C0 = eq_papp(_, _, Args)
        ;
            C0 = eq_app(_, A0, As),
            Args = [A0|As]
        ),
        sort(Args, NUVs)
    ;
        (
            C0 = eq_var(_, V)
        ;
            C0 = eq_deref(_, V)
        ;
            C0 = deref_eq(_, V)
        ;
            C0 = var_stat(V)
        ),
        NUVs = [V]
    ;
        C0 = assign(Vl, V),
        NUVs = [Vl, V]
    ),
    C = C0,
    findall(LUV, (member(LUV, NUVs), \+ord_memberchk(LUV, UVs0)), LUVs),
    sort(NUVs, NUVs1),
    ord_union(NUVs1, UVs0, UVs),
    findall(IBV, member(bang(i, IBV), Ann0), NIBVs),
    sort(NIBVs, NIBVs1),
    ord_union(NIBVs1, IBVs0, IBVs),
    Ann1 = [ibanged_later(IBVs0), last_use(LUVs), used_later(UVs0)|Ann0],
    % findall(AV, (member(AV, NUVs), \+ ord_memberchk(AV, UVs0)), LVs),
    % map('X,last_var(X)', LVs, LVAnns),
    % append(LVAnns, Ann0, Ann1),
    (LSF = last(TFn) ->
        ( C0 = var_stat(RetVar) ->
            member(typed(Tlast), Ann0),
            copy_term(Tlast, Tlastc),
            deannotate_type(Tlastc, Tlast1),
            % subsumes_chk is the name in older versions
            ( subsumes_chk(Tlast1, TFn) ->
                % writeln('   XXX'(Tlast1)),
                % writeln('   XYX'(Tlast)),
                % writeln('   XXY'(TFn)),
                Tlast1 = TFn,
                check_ho_types(Ann0, return(RetVar), TFn, Tlastc)
            ;
                print('Error: incompatible return type:'(Tlast, TFn)),
                nl,
                write_src(Ann0)
            )
        ; TFn = void ->
            true
        ;
            writeln('Error: unexpected void return type:'(TFn)),
            write_src(Ann0)
        ),
        Ann = [last_stat|Ann1]
    ;
        Ann = Ann1
    ).
add_last_anns(C0-Ann0, C-Ann, LSF, UVs0, UVs, IBVs0, IBVs) :-
    C0 = cases(V, Cases0),
    map3(add_last_anns_case(LSF, UVs0, IBVs0), IBVss1, UVss1, Cases0, Cases),
    foldr(ord_union, UVs0, UVss1, UVs1), % YYY inefficient
    foldr(ord_union, IBVs0, IBVss1, IBVs), % YYY inefficient
    C = cases(V, Cases),
    Ann = Ann0,
    ord_add_element(UVs1, V, UVs).
add_last_anns(empty_stat-Ann, empty_stat-Ann, _, UVs, UVs, IBVs, IBVs). % not needed?

% As above for cases (arg order designed for map2)
% XXX add case_def
add_last_anns_case(LSF, UVs0, IBVs0, IBVs, UVs, case_dc(DC, Arity, PArgs, S0),
% add_last_anns_case(LSF, UVs0, UVs, case_dc(DC, Arity, PArgs, S0),
                     case_dc(DC, Arity, PArgs, S)) :-
    % add_last_anns(S0, S, LSF, UVs0, UVs).
    add_last_anns(S0, S, LSF, UVs0, UVs, IBVs0, IBVs).

'X,last_var(X)'(X,last_var(X)).

% write contents of src() annotation for error messages
% (if it exists)
write_src(Anns) :-
    ( member(src(S), Anns) ->
        write('  source: '),
        writeln(S)
    ;
        true
    ).
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% type inference stuff
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% First hack:
% have assoc list of var-type.  Type can have vars and unification is
% used to instantiate them as we go.

% stub for testing
its(PS) :-
    pstat_stat(PS, S),
    empty_assoc(VTm0),
    add_typed_anns(S, S1, VTm0, VTm),
    writeln(S1),
    assoc_to_list(VTm, VTs),
    writeln(VTs).

% take stat with annotations and var-type map, return same stat with
% extra typed annotations + new VT map
% We need the types of the LHS for each assignment/equality and the target
% of cases (and the overall type for var_stat) for sharing analyis.  We
% also need the types of (arguments of) the RHS explicitly, so we can
% later check pre/post conditions (currently done with sharing analysis)
% We can instantiate the types of vars etc on the RHS (if things are
% pure) so we need copy_term to avoid the map being instantiated.  Eg,
% we can have n = nil; bs = cons(true,n); is = cons(0,n) where the type
% of n is list(T) but the instances are list(bool) and list(int).  We
% also need to do some unification (with occurs check).  Eg, for xs =
% cons(x, cons(y, nil)) we need identical instances for the types of x
% and y (ignoring sharing annotations), but because of possible
% annotations (the types might have arrows), we need to ignore the
% annotations when we do the unification, but we need to keep they there
% for later checking.
% The kind of checking we do later has an expected type (from the LHS)
% and the actual type of the thing on the RHS and we need to make sure
% the pre/post conditions are compatible.
add_typed_anns(C0-Ann0, C-Ann, VTm0, VTm) :-
    C0 = seq(Sa0, Sb0),
    add_typed_anns(Sa0, Sa, VTm0, VTm1),
    add_typed_anns(Sb0, Sb, VTm1, VTm),
    C = seq(Sa, Sb),
    Ann = Ann0.
add_typed_anns(C0-Ann0, C-Ann, VTm0, VTm) :-
    C0 = cases(V, Cases0),
    lookup_assoc(V, VTm0, TV, VTm1),
    % map_acc(add_typed_anns_case(TV), Cases0, Cases, VTm1, VTm),
    map_add_typed_anns_case(TV, Cases0, Cases, VTm1, VTms),
    % XX would be more efficient if we just returned extra elements of
    % VTm
    vt_intersection(VTms, VTm),
    C = cases(V, Cases),
    Ann = [typed(TV)|Ann0].
add_typed_anns(eq_var(Vl, Vr)-Ann0, C-Ann, VTm0, VTm) :-
    C = eq_var(Vl, VrA),
    TVl = Tl,
    TVr = Tr,
    add_typed_anns_veq(eq, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA).
add_typed_anns(eq_deref(Vl, Vr)-Ann0, C-Ann, VTm0, VTm) :-
    % XX v = *abstract a bit weird and breaks other stuff
    ( Vr = abstract ->
        writeln('Error: dereference of abstract not allowed'),
        write_src(Ann0),
        % pretend * wasn't there
        C = deref_eq(Vl, VrA),
        TVl = ref(Tl),
        TVr = Tr
    ;
        C = eq_deref(Vl, VrA),
        TVl = Tl,
        TVr = ref(Tr)
    ),
    add_typed_anns_veq(eq, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA).
add_typed_anns(deref_eq(Vl, Vr)-Ann0, C-Ann, VTm0, VTm) :-
    C = deref_eq(Vl, VrA),
    TVl = ref(Tl),
    TVr = Tr,
    add_typed_anns_veq(eq, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA).
add_typed_anns(assign(Vl, Vr)-Ann0, C-Ann, VTm0, VTm) :-
    % XX *!v := abstract a bit weird - disallow?
    C = assign(Vl, VrA), % same as deref_eq
    TVl = ref(Tl),
    TVr = Tr,
    add_typed_anns_veq(assign, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm) :-
    C = var_stat(V),
    % we allow var::type "statements" and treat them as declarations
    % they must come before the var is defined
    % XXX delete this now?
    ( member(typed(TV), Ann0) ->
        ( get_assoc(V, VTm0, _) ->
            writeln('Error: redeclaration of type for '(V)),
            write_src(Ann0)
        ;
            true
        ),
        put_assoc(V, VTm0, TV, VTm),
        Ann = Ann0
    ;
        lookup_assoc(V, VTm0, TV, VTm),
        % we add typed_rhs in case this is the last statement and
        % its converted to returnvar = V
        Ann = [typed(TV), typed_rhs(TV)|Ann0]
    ).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm) :-
    C = empty_stat, % not needed?
    Ann = Ann0,
    VTm = VTm0.
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm) :-
    C = eq_dc(Vl, DC, Arity, Args),
    % similar to applications but we extract the types differently
    dc_type(DC, Arity, TDC, TDCArgs),
    add_typed_anns_dcapp(Vl, DC, TDC, Args, TDCArgs, TDC, Ann0, Ann, VTm0, VTm).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm) :-
    C = eq_sapp(Vl, F, Args),
    nfdec_struct(F, TF),
    add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm0, VTm).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm) :-
    C = eq_papp(Vl, F, Args),
    % same as eq_sapp
    nfdec_struct(F, TF),
    add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm0, VTm).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm) :-
    C = eq_app(Vl, F, Args),
    % XX if type of Vl is not an arrow we can replace app by sapp
    % good for compilation but need to tweek sharing anal code(?)
    % same as eq_sapp except we lookup type of F in assoc
    lookup_old_assoc(F, VTm0, TF, VTm1),
    add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm1, VTm).

% for function applications (arrow types)
% XX F passed in for error message - better to pass in src
add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm0, VTm) :-
    length(Args, Arity),
    extract_ret_type(Arity, TF, TFArgs, TFR),
    add_typed_anns_dcapp(Vl, F, TF, Args, TFArgs, TFR, Ann0, Ann, VTm0, VTm).

% for applications and data constructors
% XX F passed in for error message - better to pass in src
% Example: n::list(T1); bs::list(bool); e::T->T->maybe(T) ...; m = e(n,bs)
% We need to be careful to allow instances of the types for i+n and
% propogate the instance of the return type but not change the types
% in the map.  We therefore copy the types before unification.
% Also, type unification must be done without the sharing annotations on
% arrow types because they may cause unification failure.  However,
% annotations must be put back in the unified type for later use.
% XX Its all rather messy and could do with a rethink...
add_typed_anns_dcapp(Vl, F, TF, Args, TFArgs, TFR, Ann0, Ann, VTm0, VTm) :-
    % [Vl|Args] is [LHS var| RHS vars in args of fn]
    % [TFR|TFArgs] is expected types of above from F
    (   map_acc(flip_lookup_old_assoc, Args, TPCurrs, VTm0, VTm1),
        % map(fst, TPCurrs, TCurrs), % ignore purity Pty(for now)
        TPCurrs = TCurrs,
        % strip sharing annotations to avoid unification failure
        copy_term(TCurrs, TCurrsc),
        map(deannotate_type, TCurrsc, TCurrsc1),
        % we need a separate copy of deannotated type for instance
        % checking below
        copy_term(TCurrsc1, TCurrsc2),
        copy_term(TF-TFR-TFArgs, TFc1-TFRc1-TFArgsc1),
        % xxx(a),
        unify_with_occurs_check(TCurrsc1, TFArgsc1)
    ->
        % check that !var type hasn't been instantiated
        map2(check_du_var_type_inst(Ann0), Args, TCurrsc1, TCurrsc2),
        % we put back the first annotation we see for each arrow type
        unify_first_arrows(TCurrsc, TFArgsc1),
        Tr = TFRc1
    ;
        VTm1 = VTm0,
        E =.. [F|Args],
        map_acc(flip_lookup_old_assoc, Args, TPCurrs, VTm0, _),
        writeln('ERROR: type error in arguments of application:'(E, TPCurrs, TFArgs)),
        write_src(Ann0),
        smash_type_vars(TFArgs) % proceed with some default type
        ,writeln(TFArgs)
    ),
    ( get_assoc(Vl, VTm1, TVl) -> 
        % we check if its a pre/postcondition using dynamic flag
        ( checking_pre_post ->
            true % allow redefinition in pre+post conditions
        ;
            writeln('Error: variable redefined '(Vl :: TVl)),
            write_src(Ann0)
        ),
        % XXX Singleton variable in branch: TFc,Trc,TFArgsc
        % copy_term(TF-Tr-TFArgs, TFc-Trc-TFArgsc),
        deannotate_type(Trc, Tr1),
        % subsumes_chk is the name in older versions
        ( subsumes_chk(Tr1, TVl) ->
        % (   subsumes_term(Tr1, TVl) ->
            % we unify Tr1 and TVl so we instantiate type vars in
            % Trc, so type annotation for RHS is the appropriate
            % instance but has sharing info also
            Tr1 = TVl
        ;
            writeln('Error: type error in equality:'(((Vl::TVl), (Tr)))),
            write_src(Ann0)
        ),
        check_ho_types(Ann0, Vl-F-Args, TVl, Trc),
        VTm2 = VTm1
    ;
        TVl = Tr,
        put_assoc(Vl, VTm1, TVl, VTm2)
        % XXX Singleton variable in branch: TFc,Trc,TFArgsc ?????
        % Trc = Tr,
        % TFc = TF,
        % TFArgsc = TFArgs
    ),
    % xxx(args),
    map(check_ho_types(Ann0, Vl-F-Args), TFArgs, TCurrsc),
    % we add annotations for both the fn app and dc cases - could merge?
    % typed_dc() no longer used...
    % Ann = [typed(TVl), typed_rhs(TFc), typed_dc(TCurrsc)|Ann0].
    % writeln(TVl-TFc1-TFc-TF),
    Ann1 = [typed(TVl), typed_rhs(TFc1)|Ann0],
    % if we are applying a fn, add bangs for rw implicit args,
    % check ro,rw args defined, define wo args, check fn is banged
    ( nonvar(TF), TF = arrow(_, _, _, _, _, _, _, _, ROIs, RWIs, WOIs) ->
        ( var(ROIs) -> 
            writeln(dodgey(TF)),
            TF = arrow(_, _, [], [], r, nosharing, nosharing, [], [], [], [])
            % hopefully this is enough to carry on...
        ;
            true
        ),
        map('X,bang(d,X)', RWIs, Bangs),
        append([wo(WOIs)|Bangs], Ann1, Ann),
        ( (member(I, ROIs) ; member(I, RWIs)),
            \+ get_assoc(I, VTm0, _),
            writeln('Error: undeclared implicit argument: '(F, I)),
            write_src(Ann0),
            fail
        ;
            true
        ),
        globals_type_assoc_union(WOIs, VTm2, VTm),
        ( ((ROIs = [], RWIs = [], WOIs = []) ; member(app_bang(F), Ann1)) ->
            true
        ;
            writeln('Error: application with implicit argument has no "!": '(F)),
            write_src(Ann0)
        )
    ;
        VTm = VTm2,
        Ann = Ann1
    ).

'X,bang(d,X)'(X,bang(d,X)).

% if var V has a bang annotation, check the type hasn't been further
% instantiated
check_du_var_type_inst(Ann, V, TV1, TV2) :-
    ( member(bang(_, V), Ann), \+ variant(TV1, TV2) -> % renaming ok (XXX check?)
        writeln('Error: type of updated variable instantiated'(V, TV1, TV2)),
        write_src(Ann)
    ;
        true
    ).

% equality for (possibly deref) vars
% For left and right sides we pass in var, type, and type of var.
% The latter two will be either identical vars or T and ref(T),
% depending on form of equality
add_typed_anns_veq(AEQ, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA) :-
    % type of Vr should already be known (special case for abstract)
    % if its known and not ref(_) but TVr=ref(_) its an error
    ( Vr = abstract ->
        ( get_assoc(Vl, VTm0, TVl3) ->
            VTm1a = VTm0
        ;
            % from default processing of arrow type we sometimes get
            % extra v=abstract eqns where v is only an arg for inner
            % arrows; here we just set the type to void
            put_assoc(Vl, VTm0, void, VTm1a)
        ),
        % lookup_old_assoc(Vl, VTm0, TVl3, VTm1a),
        copy_term(foo(Tl, TVl, TVl3), foo(Tlc, TVlc, TVl3c)),
        TVl3c = TVlc, % instantiates Tlc
        smash_type_vars(Tlc), % just in case...?
        VrA = abstract(Tlc),
        put_assoc(VrA, VTm1a, Tlc, VTm1)
    ;
        VrA = Vr,
        lookup_old_assoc(Vr, VTm0, TVr0, VTm1)
    ),
    ( TVr = TVr0 ->
        true
    ;
        writeln('Error: expected ref type for '(VrA, TVr0)),
        write_src(Ann0)
        % XX do something to help carry on here rather than fail?
    ),
    % if type of Vl is unknown we infer its same as VrA
    % if type of Vl is declared previously and this isn't := its an error
    % (unless its a pre/postcondition)
    % if type of Vl is declared here (via ::) we check its
    % an instance of VrA (and pre/post are compat)
    % XXX should treat this as an error now
    ( get_assoc(Vl, VTm1, TVl0) -> 
        % we check if its a pre/postcondition using dynamic flag
        ( AEQ = eq, \+ checking_pre_post ->
            writeln('Error: variable redefined '(Vl :: TVl0)),
            write_src(Ann0)
        ;
            true
        ),
% writeln(lhs_var_defined(Vl,TVl0)),
        ( TVl = TVl0 ->
            true
        ;
            writeln('Error: expected ref type for '(Vl, TVl0)),
            write_src(Ann0)
            % XX do something to help carry on here rather than fail?
        ),
        copy_term(Tr, Trc),
        deannotate_type(Trc, Tr1),
        % subsumes_chk is the name in older versions
        ( subsumes_chk(Tr1, Tl) ->
            Tr1 = Tl,
            % writeln(' ZZZ'(Tl, Tr)),
            check_ho_types(Ann0, Vl=Vr, Tl, Trc)
        ;
            writeln('Error: type error in var equality/assignment:'(((Vl::TVl), (Vr::TVr)))),
            write_src(Ann0)
        ),
        VTm = VTm1,
        Casts = []
    ; member(typed(TVl0), Ann0) ->  % :: T annotation on RHS
        % check TVl0 is lesseq general than Tr
        copy_term(Tr, Trc),
        deannotate_type(Trc, Tr1),
        % subsumes_chk is the name in older versions
        ( subsumes_chk(Tr1, TVl0) ->
            Tr1 = Tl,
            % writeln(' ZZZ'(Tl, Tr)),
            check_ho_types(Ann0, Vl=Vr, TVl0, Trc)
        ;
            writeln('Error: type error in var equality/assignment:'(((Vl::TVl), (Vr::TVr)))),
            write_src(Ann0)
        ),
        ( TVl = TVl0 -> % want instantiation?????
            true
        ;
            writeln('Error: expected ref type for '(Vl, TVl0)),
            write_src(Ann0)
            % XX do something to help carry on here rather than fail?
        ),
        put_assoc(Vl, VTm1, TVl0, VTm),
        ( Trc == Tr ->
            Casts = []
        ;
            Casts= [Vr]
        )
    ;
        (AEQ = assign -> % := with no prior assignment - dodgey
            writeln('Warning: assigned variable not previously defined '(Vl)),
            write_src(Ann0)
        ;
            true
        ),
        Tl = Tr,
        put_assoc(Vl, VTm1, TVl, VTm),
        Trc = Tr,
        Casts = []
    ),
    Ann = [typed(Tl), typed_rhs(Trc), casts(Casts)|Ann0].

% infer types for case branch
% first arg is current known type of case var
% XXX add case_def
add_typed_anns_case(TV, case_dc(DC, Arity, PArgs, S0),
                     case_dc(DC, Arity, PArgs, S), VTm0, VTm) :-
    dc_type(DC, Arity, TDC, TDCArgs),
    map('X,ref(X)', TDCArgs, TRDCArgs),
    % PArgs is (deref) pattern vars
    % TRDCArgs is expected types of above from DC with implicit refs
    map_acc(flip_lookup_assoc, PArgs, TCurrs, VTm0, VTm1),
    % map(fst, TPCurrs, TCurrs), % strip Pty
    % TCurrs is currently known types of above (vars if unknown - should
    % be unknown here - yes we shouldn't allow pattern-bound vars to
    % have types previously declared XXX check this)
    % We just extract types of args from type of TV - no need for
    % subsumption etc XX (check, including HO)
    % XX? don't need to deannotate types because args are distinct vars
    (   unify_with_occurs_check([TV|TCurrs], [TDC|TRDCArgs]) ->
        true
    ;
        writeln('Error: type error with case:'(DC/Arity -
                    [TV|TCurrs] - [TDC|TRDCArgs]))
        % XX make error message nicer here?
    ),
    add_typed_anns(S0, S, VTm1, VTm).

% take list of VTs from cases and get intersection
% XX must be a more efficient way (should be in assoc library?)...
% Asymetry wrt cases so some warnings will be missed?
vt_intersection([VTm0|VTms0], VTm) :-
    assoc_to_list(VTm0, VTs),
    empty_assoc(VTm1),
    map0_acc(add_assoc_if_in_all(VTms0), VTs, VTm1, VTm).

% check V-T is in each of VTms0 and if so, add it to VTm0
add_assoc_if_in_all(VTms0, V-T, VTm0, VTm) :-
    ( map0(check_get_assoc(V, T), VTms0) ->
        put_assoc(V, VTm0, T, VTm)
    ;
        VTm = VTm0
    ).

% check V has type T in VTs (if it has another type, issue a warning)
check_get_assoc(V, T, VTm) :-
    (get_assoc(V, VTm, T1) ->
        (T1 == T ->
            true
        ;
            writeln('Warning: same var name with different types: '(V)),
            fail
        )
    ;
        fail
    ).

% As above for list of cases - return list of case branches + VTms
map_add_typed_anns_case(_, [], [], _, []).
map_add_typed_anns_case(TV, [Case0|Cases0], [Case|Cases], VTm0, [VTm|VTms]) :-
    add_typed_anns_case(TV, Case0, Case, VTm0, VTm),
    map_add_typed_anns_case(TV, Cases0, Cases, VTm0, VTms).

% like copy_term but we first strip sharing/mutability info from arrow
% types
copy_type_term(T0, T) :-
    deannotate_type(T0, T1),
    copy_term(T1, T).

% strip sharing/mutability/implicit arg info from arrow types
% currently strip implicit arguments
deannotate_type(T0, T) :-
    ( var(T0) ->
        T = T0
    ; T0 = arrow(TL0, TR0, _, _, _, _, _, _, ROIs, RWIs, WOIs) ->
        deannotate_type(TL0, TL),
        deannotate_type(TR0, TR),
        T = arrow(TL, TR, _, _, _, _, _, _, ROIs, RWIs, WOIs)
    ;
        T0 =.. [F|As0],
        map(deannotate_type, As0, As),
        T =.. [F|As]
    ).

% take two types which have been unified, the first without annotations,
% and "unify", instantiating the second type to include the first
% annotation we see for each var which must be bound to an arrow type
unify_first_arrows(T0, T) :-
    ( (var(T0); var(T)) ->
        T = T0
    ; T0 = arrow(TL0, TR0, A0, B0, C0, D0, E0, F0, G0, H0, I0) ->
        T = arrow(TL, TR, A, B, C, D, E, F, G, H, I),
        ( var(A) ->
            % from first occurrence of a var - add annotations from T0
            A = A0,
            B = B0,
            C = C0,
            D = D0,
            E = E0,
            F = F0,
            G = G0,
            H = H0,
            I = I0
        ;
            % already instantiated - ignore annotations from T0
            true
        ),
        unify_first_arrows(TL0, TL),
        unify_first_arrows(TR0, TR)
    ;
        T0 =.. [F|As0],
        T =.. [F|As],
        map(unify_first_arrows, As0, As)
    ).

'X,ref(X)'(X,ref(X)).

% lookup_assoc with last two args flipped
flip_lookup_assoc(V, TV, VTm0, VTm) :-
    lookup_assoc(V, VTm0, TV, VTm).

% lookup_old_assoc with last two args flipped
flip_lookup_old_assoc(V, TV, VTm0, VTm) :-
    lookup_old_assoc(V, VTm0, TV, VTm).

% find type from data constructor/arity
% XX requires search - should be faster
dc_type(DC, Arity, TDC, TArgs) :-
    ( number(DC) -> % XXX handle floats also
        TDC = int,
        TArgs = []
    ;
        length(TArgs, Arity),
        tdef(TDC, DCTs),
        member(dcons(DC, TArgs), DCTs)
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% type defns -> type representation for sharing analysis
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% Current structure for representing types for sharing purposes.
% Here we only represent ground types (no parameters).  We have sum and
% product nodes.  Sum nodes represent types, which have a list of data
% constructors (product nodes).  Product nodes are data constructors
% with lists of args which are types (sum nodes).  We have explicit ref
% nodes (sum and product).  This makes some things clearer and
% allows refs to refs etc with no extra work.  Ref nodes are a bit special
% because they are the focus of sharing analysis - we are interested in
% what sets of ref nodes can intersect.  For sum nodes we keep track of the
% name of the type so later we can partition sharing sets into different
% types for efficiency.  Sum nodes can also be represented by a reference
% to an ancestor sum node in the tree (we specify how many levels of sum
% nodes up the tree we go).  This is to makes type representation finite
% and the representation of sharing finite (and inevitably less precise).
% In the code we traverse down the type representation but also keep track
% of the list of ancestor nodes so we can jump back up the tree.
% The type representation in its most general form could be described
% as follows (it once was but itsn't any more - see below):
% And see later for higher order.
% 
% :- type sum --->
%     sum(type_name, list(prod)) ;
%     sum_anc(int). % ancestor node
% :- type prod ---> prod(data_cons, arity, list(sum)).
% 
% However, we specialise type sum so it has more similar structure to the
% code for sharing analysis, where ref nodes are special.  We use
% :- type sum --->
%     sum(type_name, list(prod)) ; % not used for refs
%     ref(type_name, sum) ; % like sum(type_name, [prod('_ref', 1, [sum])]) above
%     ref_anc(int). % like sum(??, [prod('_ref', 1, sum_anc(int))]) above
% 
% Note also that at the top level we can't have ref_anc(i) (i>=2 generally
% so these nodes must be lower in the tree).  This isn't encoded in the
% type.  Also not encoded is the constraint that "sum" node children of
% types defined with sum/2 must be defined by either ref or ref_anc nodes
% (the arguments of "normal" data constructors must be refs; we
% also allow refs to refs to refs etc, which doesn't correspond so
% directly to a traditional ADT).
% 
% Example from wam.pns (contains mutual recursion):
% type fs ---> f0 ; f1 ; f2.
% type term ---> var(term) ; nv(fs, terms).
% type terms ---> nil ; cons(term, terms).
% Gives the following representation:
% type_struct(fs,
%     sum(fs, [prod(f0, 0, []), prod(f1, 0, []), prod(f2, 0, [])])).
% type_struct(term, sum(term,
%     [prod(var, 1, [ref_anc(2)]),
%      prod(nv, 2, [ref(ref(fs), sum(fs,
%         [prod(f0, 0, []), prod(f1, 0, []), prod(f2, 0, [])])),
%         ref(ref(terms), sum(terms,
%             [prod(nil, 0, []), prod(cons, 2, [ref_anc(4), ref_anc(2)])]))])])).
% type_struct(terms, sum(terms,
%     [prod(nil, 0, []),
%      prod(cons, 2, [ref(ref(term), sum(term,
%         [prod(var, 1, [ref_anc(2)]),
%          prod(nv, 2, [ref(ref(fs), sum(fs,
%             [prod(f0, 0, []), prod(f1, 0, []), prod(f2, 0, [])])),
%             ref_anc(4)])])),
%         ref_anc(2)])])).
%
% Note that the representation for term is not the same as the
% nested sum node which represents term inside the representation of
% terms, and the representation of terms is not the same as the nested
% one inside term.  Although polymorphic types are nice, its not clear
% how a polymorphic version of the sharing for the list type can be done
% so it supports these two different representations for a list of
% terms.
%
% Higher order: we also have another kind of sum for arrow types:
% arrow(TypeL, TypeR, BangVs, Params, Resvar, Pre, Post, ClaTypes,
% _ROIs, _RWIs, _WOIs)
% For closure arguments we fudge things so they appear to have function
% symbols cla(1), cla(2),... with a single argument used for sharing
% info (we use eg cla(1) rather than cla(1).'_ref' for shared paths).

% We generate type_structs on demand and cache them using dynamic
% procedure type_struct_c
% For arrow types we just pass them though and convert them to
% sharing representation later (possibly multiple times, so we can
% handle multiple instances of higher order functions) XX
type_struct(T, S) :-
    ( var(T) ->
        writeln('ERROR: type_struct called with variable'),
        type_struct(ref(void), S)
    ; T = arrow(_, _, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) ->
        S = T
    ; type_struct_c(T, S1) ->
        S = S1
    ; tdef_tdef_struct(_TDs, T, type_struct(T, S)) ->
        assert(type_struct_c(T, S))
    ;
        writeln('Error: undefined type, void assumed: '(T)),
        type_struct(void, S)
    ).

:- dynamic(type_struct_c/2).

% takes list of all type defs XX now asserted in tdef/2
% (first arg is now unused)
%  + a type name and returns type_struct for
% that type (for sharing analysis)
tdef_tdef_struct(TDefs, TName, TS) :-
    ( TName = arrow(_, _, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) ->
        TS = TName
    ;
        TS = type_struct(TName, Sum),
        % member(tdef(TName, CTs), TDefs),
        tdef(TName, CTs),
        type_sum(TDefs, [], TName, CTs, Sum)
    ).

% Need special case for ref/1
type_sum(TDefs, Ancs, TName, CTs, Sum) :-
    ( TName = arrow(_, _, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) -> % not needed?
        Sum = TName
    ; TName = ref(TName1) ->
        type_ref_sum(TDefs, [TName|Ancs], TName1, Sum)
    ;
        Sum = sum(TName, Prods),
        map(cons_types_prod(TDefs, [TName|Ancs]), CTs, Prods)
    ).

cons_types_prod(TDefs, Ancs, dcons(DC, Ts), prod(DC, Arity, Sums)) :-
    Ancs = [TName|_],
    length(Ts, Arity),
    map(type_ref_sum(TDefs, [ref(TName)|Ancs]), Ts, Sums).

type_ref_sum(TDefs, Ancs, TName, Sum) :-
    ( nth1(N, Ancs, TName) ->
        Sum = ref_anc(N)
    ;
        Sum = ref(ref(TName), Sum1),
        % member(tdef(TName, CTs), TDefs),
        ( TName = arrow(_, _, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) ->
            Sum1 = TName
        ;
            tdef(TName, CTs),
            type_sum(TDefs, Ancs, TName, CTs, Sum1)
        )
    ).

% get unique/fresh var
fresh_var(V) :-
    % random(R), % not supported in some versions
    % I is round(R*100000),
    % I is random(1000000),
    retract(var_number(I)), % less robust
    % var_number(I),
    % retractall(var_number(_)),
    I1 is I + 1,
    assert(var_number(I1)),
    name(I, Cs),
    name(V, [0'V|Cs]).

:- dynamic(var_number/1), retractall(var_number(_)).
var_number(0).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Sharing/alias analysis prototype
% we use ord_sets of s(varpath1, varpath2) where varpath1 @=< varpath2
% and varpath = vp(varname,vpc(dcons, arity, argnum, vpc(... vpe)))
% (vpc=var path constructor, vpe=var path empty)
% XX could use var - [caa(dcons, arity, argnum), caa(...), ...]
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% given LVP, a path for LHS of :=, the list of extended paths considered
% for it when RHS of := is traversed and list of var paths which are aliases
% for LVP, add sharing pairs between extended LVP paths and similarly
% extended paths for the aliases
add_sharing_for_lhs_aliases(_LVP, [], _AVPs, SS, SS).
add_sharing_for_lhs_aliases(LVP, [ELVP|ELVPs], AVPs, SS0, SS) :-
    app_var_path(LVP, RestVPC, ELVP),
    add_sharing_for_lhs_aliases1(ELVP, RestVPC, AVPs, SS0, SS1),
    add_sharing_for_lhs_aliases(LVP, ELVPs, AVPs, SS1, SS).

% as above for single "extension" of LVP path
add_sharing_for_lhs_aliases1(_ELVP, _VPC, [], SS, SS).
add_sharing_for_lhs_aliases1(ELVP, VPC, [AVP|AVPs], SS0, SS) :-
    app_var_path(AVP, VPC, EAVP),
    mk_alias_pair(ELVP, EAVP, S),
    mk_alias_pair(ELVP, ELVP, S1),
    mk_alias_pair(EAVP, EAVP, S2),
    add_sharing_for_lhs_aliases1(ELVP, VPC, AVPs, [S1,S2,S|SS0], SS).

% Get subset of (precond) sharing which has a path with var from list
% (of DU args) - this needs to be added to postcondition
filter_sharing_member(PreSS, DUs, SS) :-
    filter(sharing_member(DUs), PreSS, SS).

% Share pair has path with var from list
sharing_member(DUs, s(vp(V1, _), vp(V2, _))) :-
    (   member(V1, DUs)
    ;   member(V2, DUs)
    ).

% Get subset of (postcond) sharing which has a path with var from list
% (of DU args + ret var) or abstract
filter_sharing_abs_member(PreSS, DUs, SS) :-
    filter(sharing_abs_member(DUs), PreSS, SS).

% Share pair has path with var from list, or abstract
sharing_abs_member(DUs, s(vp(V1, _), vp(V2, _))) :-
    (   member(V1, [abstract(_)|DUs])
    ;   member(V2, [abstract(_)|DUs])
    ).

% Get subset of sharing which has both paths with vars from list
% (of DU args/result) or abstract
filter_sharing_both_member(PreSS, DUs, SS) :-
    filter(sharing_both_member(DUs), PreSS, SS).

% Share pair has both paths with var from list or abstract
sharing_both_member(DUs, s(vp(V1, _), vp(V2, _))) :-
    (   member(V1, DUs)
    ;
        V1 = abstract(_)
    ),
    (   member(V2, DUs)
    ;
        V2 = abstract(_)
    ).

% checks both vars in share pair are relevant to args/result vars of a
% call
% XX should allow prefixes of paths???
% XX reconsider efficiency
pair_in_var_list(s(vp(V1, _), vp(V2, _)), ResArgs) :-
    member(vp(V1, _), ResArgs),
    member(vp(V2, _), ResArgs).

% given "banged" vars, possibly modified vars and current alias info,
% check all appropriate vars are "banged"
% XX Currently writes any error messages then succeeds
% XX best collect offending vars in another setof so we don't
% print statement for each var
% XXX conservative: for each var path which can be modified, ideally
% we should retain more information about which sub-paths can be
% modified.  Eg, if only the top level path can be modified we can be
% more precise.  Eg, l := cons(a, l) can modify l but it can't modify
% things which share with the elements of l.  In general, things lower
% in type tree are safe from modification - could check length of var
% paths etc.  We now specialise for LHS of assignment statements at
% least (see _lhs preds below).
% XXX currently pass in annotations to see what vars are used later
% - should really just be removing all these from sharing set (need to
% keep track of what vars we need to keep for pre/postconditions
% though).
% Elsewhere we check all calls with implicit args are banged - we use
% app_bang annotations rather than bang for these
check_banged(BVs, MVs, SS, Ann, Stat) :-
    ( setof(MV, should_bang(MVs, SS, MV), Vs1) -> % Note setof can fail
        check_banged1(BVs, Vs1, SS, Ann, Stat)
    ;
        true
    ).

% as above, specialised for single modified var on LHS of assignment
% XX probably should bang LV even if its not used (or give warning)
check_banged_lhs(LV, BVs, SS, Ann, Stat) :-
    (   setof(MV, should_bang_lhs(LV, SS, MV), Vs1) -> % Note setof can fail
        check_banged1(BVs, Vs1, SS, Ann, Stat)
    ;
        true
    ).

% as above with all possibly modified vars
check_banged1(BVs, AMVs, SS, Ann, Stat) :-
    % iterate over all members of AMVs
    (   member(V, AMVs),
        % skip error messages about V* (introduced) vars
        (( atomic(V), % in case its abstract(_)
            name(V, VS),
            name('V', VCodes),
            append(VCodes, _, VS)
        ) ->
            fail
        ;
            true
        ),
        % ignore dead vars (use -> in case used_later() is missing)
        % note we allow update of dead vars which share with abstract -
        % this allows greater flexibility in coding and there are
        % reasonable uses of it.  note abstract() gets ignored here
        ( member(used_later(ULVs), Ann) ->
            member(V, ULVs)
        ;
            true
        ),
        % we check for du of abstract vars, even if they are banged
        % note we need to check for sharing with abstract, not
        % V=abstract(_)
        ( aliases(SS, vp(V, _), vp(abstract(_), _)) ->
            write('Error: abstract variable '),
            print(V),
            write(' may be modified by '),
            print(Stat),
            nl,
            write_src(Ann),
            fail
        ;
            true
        ),
        % ignore banged vars
        \+ member(V, BVs),
        % must be an error...
        write('Error: variable '),
        write(V),
        write(' might be modified by '),
        print(Stat),
        nl,
        write_src(Ann),
        fail
    ;
        true
    ).

% given list of varpaths which may be modified, and sharing set,
% (nondeterministically) return var path which may be modified
should_bang(MVs, SS, MV) :-
    member(vp(MV1, _P3), MVs),
    (   MV = MV1
    ;
        member(s(vp(MV1, _), vp(MV, _)), SS)
    ;
        member(s(vp(MV, _), vp(MV1, _)), SS)
    ).

% as above, specialised for single modified var on LHS of assignment
should_bang_lhs(vp(LMV, LVP), SS, MV) :-
    vpc_length(LVP, LN),
    (   MV = LMV
    ;
        member(s(vp(LMV, VP1), vp(MV, _)), SS),
        vpc_length(VP1, N1),
        N1 =< LN
    ;
        member(s(vp(MV, _), vp(LMV, VP2)), SS),
        vpc_length(VP2, N2),
        N2 =< LN
    ).

% % Given two lists of var paths and alias set, see if there is any
% % aliasing between pairs of var paths in the two lists
% any_aliasing(VPs1, VPs2, SS) :-
%     member(VP1, VPs1),
%     member(VP2, VPs2),
%     (   VP1 = VP2
%     ;
%         mk_alias_pair(VP1, VP2, SP),
%         % ord_member(SP, SS) % undefined in some versions
%         member(SP, SS)
%     ).

% given two alias sets, find additional set of "transitive" edges,
% avoiding adding bogus aliasing of different data constructor arguments
% eg, the first argument of a pair is never an alias of the second
% argument of a pair or the first argument of a cons, even though they
% may all be aliases for the same (explicit) ref - see
% incompatible_dc_path
% Note: setof fails if goal fails so we need a special case
% Note: setof returns an ordset (if we change set representation
% this code may have to be changed)
transitive_aliasing(SS0, NSS, TSS) :-
    ( setof(TS, trans_alias_1(SS0, NSS, TS), TSS1) ->
        TSS = TSS1
    ;
        TSS = []
    ).

% as above, but return one edge/pair at a time, using backtracking
% Note the graph is undirected so we need disjunctions
% (XX could lift member calls outside disjunctions for efficiency)
trans_alias_1(SS0, NSS, SP) :-
    (   member(s(VP1, VP2), SS0)
    ;
        member(s(VP2, VP1), SS0)
    ),
    VP1 \= VP2, % ignore self-aliasing - won't lead to new pair
    (   member(s(VP2, VP3), NSS)
    ;
        member(s(VP3, VP2), NSS)
    ),
    VP3 \= VP2, % ignore self-aliasing - won't lead to new pair
    VP1 \= VP3, % don't add self-aliasing
    \+ incompatible_dc_path(VP1, VP3), % no alias of different DC args
    mk_alias_pair(VP1, VP3, SP).

% one (bidirectional) edge in graph - generator
% (XX could increase efficiency, depending on instantiation)
% XX refactor above (and elsewhere?)
aliases(SS, VP1, VP2) :-
    (   member(s(VP1, VP2), SS)
    ;
        member(s(VP2, VP1), SS)
    ).

% the Nth arg of data constructor D can only be aliased to the same,
% or to an arbitrary ref (ie explicit ref rather than implicit one).
% Here we check if two var paths have two components at the end which
% are incompatible (second last components are not ref and not the same)
incompatible_dc_path(VP1, VP2) :-
    app_var_path(_, vpc(C1, A1, N1, vpc('_ref', 1, 1, vpe)), VP1),
    app_var_path(_, vpc(C2, A2, N2, vpc('_ref', 1, 1, vpe)), VP2),
    \+ (C1 = '_ref', A1 = 1, N1 = 1),
    \+ (C2 = '_ref', A2 = 1, N2 = 1),
    \+ (C1 = C2, A1 = A2, N1 = N2).

% Union of two sharing sets with transitivity added
sharing_union(SS0, SS1, SS) :-
    transitive_aliasing(SS0, SS1, SST),
    ord_union(SS0, SST, SS0T),
    ord_union(SS0T, SS1, SS).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% defined arity of each function
:- dynamic(func_arity/2).

% for functions defined in C
:- dynamic(c_fn_def/2).

% for extern functions
:- dynamic(extern_fn/1).

% maximum closure arguments (max function arity minus one)
:- retractall(max_cl_args(_)).  % in case we load this file more than once
:- dynamic(max_cl_args/1).
max_cl_args(2).

% given ariry of new fn defn, update above
% (ignore for closure - should pass in fn XX)
update_max_cl_args(A) :-
    A1 is A - 1,
    max_cl_args(CA),
    (A1 > CA, \+ builtin_func_arity(closure, A) ->
        retractall(max_cl_args(_)),
        assert(max_cl_args(A1))
    ;
        true
    ).

% append for var paths
app_var_path(vp(V, VPC1), VPC2, vp(V, VPC)) :-
    app_vpc(VPC1, VPC2, VPC).

% as above for constructor part
app_vpc(vpe, VPC, VPC).
app_vpc(vpc(C, A, N, VPC1), VPC2, vpc(C, A, N, VPC)) :-
    app_vpc(VPC1, VPC2, VPC).

% drop last N things in var path
var_path_drop_last(N, vp(V, VPC0), vp(V, VPC)) :-
    vpc_drop_last(N, VPC0, VPC).

vpc_drop_last(N, VPC0, VPC) :-
    vpc_length(VPC0, N1),
    N2 is N1 - N,
    vpc_keep(N2, VPC0, VPC).

% length for constructor part of var path
vpc_length(vpe, 0).
vpc_length(vpc(_, _, _, VPC0), N) :-
    vpc_length(VPC0, N1),
    N is N1 + 1.

% drop all but first N for constructor part
vpc_keep(0, _, vpe).
vpc_keep(N, vpc(C, A, AN, VPC0), vpc(C, A, AN, VPC)) :-
    N > 0,
    N1 is N - 1,
    vpc_keep(N1, VPC0, VPC).

% drop first N of constructor path
% vpc_drop(0, VPC, VPC).
% vpc_drop(N, vpc(_, _, _, VPC0), VPC) :-
%     N > 0,
%     N1 is N - 1,
%     vpc_drop(N1, VPC0, VPC).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% various low level stuff for aliasing
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% make alias pair from two varpaths
mk_alias_pair(VP1, VP2, S) :-
    % compare/3 broken for compound terms in SWI-Prolog it seems...
    % compare(VP1, VP2, R),
    ( VP1 @=< VP2 -> % allow self-aliases?
    % ( VP1 @< VP2 -> % disallow self-aliases
        S = s(VP1, VP2)
    ; VP1 @> VP2 ->
        S = s(VP2, VP1)
%     ; % hack to avoid multiple self alias pairs
%         S = s(vp('_', vpe), vp('_', vpe))
    ).

% deterministic version - more flexible nondet code below
% % return all path which may share corresponding to a type
% % YY:-( gave up on attempt at clever efficient coding (with more sharing and
% % less appending)
% type_paths(T, Ps) :-
%     type_struct(T, TS),
%     type_paths_sum(vpe, TS, Ps1),
%     sort(Ps1, Ps). % remove any dups from multiple ref_anc()
% 
% % as above for sum type, given path so far to prefix
% type_paths_sum(P0, sum(_, Prod), Ps) :-
%     map0_acc(type_paths_prod(P0), Prod, [], Ps).
% type_paths_sum(P0, ref(_, Sum), [P|Ps]) :-
%     app_vpc(P0, vpc(ref, 1, 1, vpe), P),
%     type_paths_prod(P0, prod(ref, 1, [Sum]), [], Ps).
% type_paths_sum(P0, ref_anc(N), [P]) :-
%     N1 is N - 1,
%     vpc_drop_last(N1, P0, P).
% type_paths_sum(P0, arrow(_, _TypeR, _, _, _, _, _, _, _ROIs, _RWIs,
% _WOIs), Ps) :-
%     max_cl_args(NCA),
%     % XX could find number of arrows in TypeR and subtract this from NCA
%     type_paths_clas(NCA, CAPs),
%     map(app_vpc(P0), CAPs, Ps).
% 
% % return given number of closure arg paths
% type_paths_clas(N, Ps) :-
%     ( N =< 0 ->
%         Ps = []
%     ;
%         N1 is N - 1,
%         Ps = [vpc(cla(N), 1, 1, vpe)|Ps1],
%         type_paths_clas(N1, Ps1)
%     ).
% 
% % as above for prod type (list of DCs), with accumulator
% type_paths_prod(P0, prod(DC, Arity, Sums), Ps0, Ps) :-
%     type_paths_dc(P0, DC, Arity, 1, Sums, Ps0, Ps).
% 
% % as above for all (remaining) arg(s) of DC
% type_paths_dc(_P0, _DC, _Arity, _N, [], Ps, Ps). % N = Arity+1
% type_paths_dc(P0, DC, Arity, N, [Sum|Sums], Ps0, Ps) :-
%     type_paths_dc_arg(P0, DC, Arity, N, Sum, Ps0, Ps1),
%     N1 is N + 1,
%     type_paths_dc(P0, DC, Arity, N1, Sums, Ps1, Ps).
% 
% % as above for single arg
% type_paths_dc_arg(P0, DC, Arity, N, Sum, Ps0, Ps) :-
%     app_vpc(P0, vpc(DC, Arity, N, vpe), P),
%     type_paths_sum(P, Sum, DCSPs),
%     append(DCSPs, Ps0, Ps).

% return var self-sharing corresponding to a type (not sorted)
type_var_self_share(T, V, Ss) :-
    type_var_paths(T, V, VPs),
    map(self_alias, VPs, Ss).

% return all var paths which may share corresponding to a type
type_var_paths(T, V, VPs) :-
    type_paths(T, Ps),
    map(mk_vp(V), Ps, VPs).

mk_vp(X,P,vp(X,P)).

% return all paths which may share corresponding to a type
% YY might be worth caching this
type_paths(T, Ps) :-
    ( setof(TP, P^trunc_type_path(T, P, TP), Ps) ->
        true
    ;
        Ps = []
    ).

% for type T, P is a path which may be too long (end corresponding to a
% ref_anc() node) and TP is the corresponding truncated path.  Can
% generate all TP values given just T (not all P values returned in this
% mode); may have duplicate solutions.
trunc_type_path(T, P, TP) :-
    type_struct(T, TS),
    trunc_type_path_sum(TS, P, N),
    vpc_drop_last(N, P, TP).

% as above for sum type; returns number of items in path to drop
% We first have a special case for when we input P=vpe
trunc_type_path_sum(Sum, P, N) :-
    % XXX yuk so we can pass in P==vpe
    ( P == vpe -> % nonvar(P)
        trunc_type_path_sum(Sum, P1, N1),
        vpc_length(P1, N1),
        N = 0
    ;
        trunc_type_path_sum1(Sum, P, N)
    ).

% as above but P\==vpe
trunc_type_path_sum1(sum(_, Prod), P, N) :-
    trunc_type_path_prod(Prod, P, N).
trunc_type_path_sum1(ref(_, Sum), P, N) :-
    P = vpc('_ref', 1, 1, P1),
    (   P1 = vpe,
        N = 0
    ;
        trunc_type_path_sum(Sum, P1, N)
    ).
trunc_type_path_sum1(ref_anc(N), P, N1) :-
    % XXX yuk so we can use this code to generate all
    % possible truncated paths for a given type, if P is a var
    % we commit to a single path for it, otherwise there can be
    % a large number of paths and we don't know what they are here since
    % ref_anc() doesn't tell us the type (could change type
    % representation so ref_anc() has type name I guess)
    ( var(P) ->
        P = vpc('_ref', 1, 1, vpe)
    ;
        true
    ),
    vpc_length(P, L),
    N1 is N + L - 1.
trunc_type_path_sum1(arrow(_, _TypeR, _, _, _, _, _, _, _ROIs, _RWIs,
_WOIs), P, 0) :-
    % XXX yuk again
    ( var(P) ->
        P = vpc(cla(CAN), 1, 1, vpe),
        max_cl_args(NCA),
        % XX could find number of arrows in TypeR and subtract this from NCA
        between(1, NCA, CAN)
    ;
        true
    ).

% as above for prod type (list of DCs)
trunc_type_path_prod(DCs, vpc(DC, Arity, AN, P1), N) :-
    member(prod(DC, Arity, Sums), DCs),
    between(1, Arity, AN),
    nth1(AN, Sums, Sum),
    trunc_type_path_sum(Sum, P1, N).

% we want to remove (fail here) sharing of Var if Arity=0 or the
% DC/Arity don't match the path
% Note that for recursive types we have to be careful.  For example, for
% binary trees with data in leaves, DC branch/2 matches leaf/1 because
% (with current precision of paths) the args of branch/2 are ref_anc
% nodes which are the same as the empty path.
% Easiest to express negatively..
% Maybe fix this so we use var paths as noted somewhere?
% XX does it really have to be this complicated?/can we refactor?
alias_var_dcons_ok(Var, DC, Arity, SP) :-
    \+ alias_var_dcons_to_rm(Var, DC, Arity, SP).

% Succeeds if we want to drop this alias pair
alias_var_dcons_to_rm(Var, _DC, 0, s(vp(Var, _), _)).
alias_var_dcons_to_rm(Var, _DC, 0, s(_, vp(Var, _))).
alias_var_dcons_to_rm(Var, DC, Arity, s(vp(Var, vpc(DC1, Arity1, _, _)), _)) :-
    (   DC \= DC1
    ;
        Arity \= Arity1
    ),
    \+ has_ref_anc(DC, Arity).
alias_var_dcons_to_rm(Var, DC, Arity, s(_, vp(Var, vpc(DC1, Arity1, _, _)))) :-
    (   DC \= DC1
    ;
        Arity \= Arity1
    ),
    \+ has_ref_anc(DC, Arity).

% check if DC/Arity is in type with recursion to node at or above this
% DC/Arity.  Eg for branch/2 its true.
% May succeed more than once (but we only call this inside \+)
has_ref_anc(DC, Arity) :-
    type_struct_c(_Type, sum(_T, Prods)),  % XX need search to find type:-(
    Prod = prod(DC, Arity, Sums),
    member(Prod, Prods),
    member(Sum, Sums),
    has_ref_anc_sum(Sum, 2).

% type has reference to ancestor >= D
has_ref_anc_sum(ref_anc(N), D) :-
    N >= D.
has_ref_anc_sum(ref(_, sum(_, Sums)), D) :-
    D1 is D + 2,
    member(Sum, Sums),
    has_ref_anc_sum(Sum, D1).
has_ref_anc_sum(sum(_, Prods), D) :-
    D1 is D + 2,
    member(prod(_, _, Sums), Prods),
    member(Sum, Sums),
    has_ref_anc_sum(Sum, D1).

% remove all aliases for particular var
rm_all_var_aliases(Var, SS0, SS) :-
    filter(alias_var_different(Var), SS0, SS).

% var different from both vars in alias pair
alias_var_different(V1, s(vp(V2, _), vp(V3, _))) :-
    V1 \= V2,
    V1 \= V3.

% find list of var paths which alias with LVP
% ignore self-aliases
var_ref_alias_vps(LVP, SS, AVPs) :-
    % XX filter+map
    ( setof(AVP, S^(member(S, SS), var_ref_alias_vp(LVP, S, AVP)), AVPs1) ->
        AVPs = AVPs1
    ;
        AVPs = []
    ).

% as above for single var/pair
var_ref_alias_vp(LVP, s(LVP, AVP), AVP) :-
    LVP \= AVP.
var_ref_alias_vp(LVP, s(AVP, LVP), AVP) :-
    LVP \= AVP.

% find list of vars which share with LVar.'_ref'/1
% ignore self-aliases
% XX rename (share->alias) and define in terms of var_ref_alias_vps
var_ref_shared_vars(LVar, SS, SVars) :-
    % XX filter+map
    ( setof(Var, S^(member(S, SS), var_ref_shared_var(LVar, S, Var)), SVars1) ->
        SVars = SVars1
    ;
        SVars = []
    ).

% as above for single var/pair
var_ref_shared_var(LVar, s(vp(LVar, vpc('_ref', 1, 1, vpe)), vp(Var, _)), Var) :-
    Var \= LVar.
var_ref_shared_var(LVar, s(vp(Var, _), vp(LVar, vpc('_ref', 1, 1, vpe))), Var) :-
    Var \= LVar.

% remove all aliases for particular var
% except ones for SVars
rm_unshared_var_ref_aliases(Var, SVars, SS0, SS) :-
    filter(not_unshared_var_ref_alias(Var, SVars), SS0, SS).

% sharing pair not between V1 and var not in SVars
not_unshared_var_ref_alias(V1, SVars, s(vp(V2, _), vp(V3, _))) :-
    \+ (
        V2 = V1,
        \+ member(V3, SVars)
    ;
        V3 = V1,
        \+ member(V2, SVars)
    ).

% rename vars in sharing pairs of formal parameters (first param = result)
% XXX should sort result here rather than calling sort whenever this is
% called
% XX could probably code abstract handling better...
rename_sharing([], _, _, []).
rename_sharing([s(vp(N1, P1), vp(N2, P2))|SS], FAs, Args, SSArgs) :-
    ((  nth0(AN1, FAs, N1),
        nth0(AN1, Args, vp(V1, VP1)),
        nth0(AN2, FAs, N2),
        nth0(AN2, Args, vp(V2, VP2)),
        app_var_path(vp(V1, VP1), P1, Var1),
        app_var_path(vp(V2, VP2), P2, Var2)
    ) ->
        mk_alias_pair(Var1, Var2, S),
        SSArgs = [S|SSArgs1]
    ; ( N1 = abstract(_),
        Var1 = vp(N1, P1),
        nth0(AN2, FAs, N2),
        nth0(AN2, Args, vp(V2, VP2)),
        app_var_path(vp(V2, VP2), P2, Var2)
    ) ->
        mk_alias_pair(Var1, Var2, S),
        SSArgs = [S|SSArgs1]
    ; ( N2 = abstract(_),
        Var2 = vp(N2, P2),
        nth0(AN1, FAs, N1),
        nth0(AN1, Args, vp(V1, VP1)),
        app_var_path(vp(V1, VP1), P1, Var1)
    ) ->
        mk_alias_pair(Var1, Var2, S),
        SSArgs = [S|SSArgs1]
    % XX do we need to include abstract self-aliasing here?
    % need to include it somewhere and here wont do any harm...
    ; ( N2 = abstract(T),
        Var2 = vp(N2, P2),
        N1 = abstract(T),
        Var1 = vp(N1, P1)
    ) ->
        mk_alias_pair(Var1, Var2, S),
        SSArgs = [S|SSArgs1]
    ;
% XX we allow/ignore extra vars in pre/post sharing
        SSArgs = SSArgs1
    ),
    rename_sharing(SS, FAs, Args, SSArgs1).

% as above but just for vars which are DU
% XXX support more general var paths for declaring DU eventually...
rename_vars([], _,  _, []).
rename_vars([PV|PVs], FAs, Args, [V1|Vs]) :-
    nth0(N1, FAs, PV),
    nth0(N1, Args, V1),
    rename_vars(PVs, FAs, Args, Vs).

%%%%%%
% dead(var) - just remove all associated aliases
% XX not used but we should eventually
alias_dead(Var, SS0, SS) :-
    rm_all_var_aliases(Var, SS0, SS).

% for testing
sa(S) :-
    infer_post(S, SS),
    print(SS), 
    nl,
    fail.

% for testing
% infer postcond for stat, assuming empty precond
% XX generally want some type info passed in...
infer_post(PS, SS) :-
    pstat_stat(PS, S),
    % empty_assoc(VTm0),
    globals_type_assoc([], VTm0),
    add_typed_anns(S, S1, VTm0, _VTm),
    smash_type_vars(S1), % XX?
    % add_last_anns not needed but last_use anns can speed things up
    add_last_anns(S1, S2, last(_), [], _UVs, [], _IBVs),
    % xxx(infer_post),
    % writeln(S2),
    alias_stat(S2, [], SS).

% XX function declarations currently asserted rather than being passed
% around: just fname and canonical type stored
:- dynamic(nfdec_struct/2).

% XX function definitions currently asserted rather than being passed
% around
% fn_def_struct(Fn, Args, Stat),
:- dynamic(fdef_struct/3).

fn_def_struct(A, B, C) :- fdef_struct(A, B, C).

%%%%%%
% Overall handling of statements for sharing analysis
% XXX should remove alias info from dead vars some time
alias_stat(C-_Ann, SS0, SS) :-
    C = empty_stat, % not needed?
    SS = SS0.
alias_stat(C-_Ann, SS0, SS) :-
    C = seq(Sa, Sb),
    alias_stat(Sa, SS0, SS1),
    alias_stat(Sb, SS1, SS).
alias_stat(C-Ann, SS0, SS) :-
    C = eq_var(Vl, Vr),
    VPl = vp(Vl, vpe),
    VPr = vp(Vr, vpe),
    % xxx(as),
    alias_stat_veq(VPl, VPr, Ann, SS0, SS),
    % if Vr has different type to Vl we have a cast and if there is
    % any sharing introduced between these vars we must not implicitly
    % mutate Vr later
    % XXXX add this check to DC and applications also (or everything)
    (   member(casts([Vr]), Ann),
        SS0 \== SS, % XX inefficient if SS0 big
        member(ibanged_later(IBVs), Ann),
        member(Vr, IBVs)
    ->
        writeln('Error: sharing of cast variable later implicitly mutated '(Vr)),
        write_src(Ann)
    ;
        true
    ).
alias_stat(C-Ann, SS0, SS) :-
    C = eq_deref(Vl, Vr),
    VPl = vp(Vl, vpe),
    VPr = vp(Vr, vpc('_ref', 1, 1, vpe)),
    alias_stat_veq(VPl, VPr, Ann, SS0, SS).
alias_stat(C-Ann, SS0, SS) :-
    C = deref_eq(Vl, Vr),
    VPl = vp(Vl, vpc('_ref', 1, 1, vpe)),
    VPr = vp(Vr, vpe),
    alias_stat_veq(VPl, VPr, Ann, SS0, SS).
alias_stat(C-Ann, SS0, SS) :-
    C = assign(Vl, Vr),
    member(typed(T), Ann),
    % type_struct(T, Sum),
    VPl = vp(Vl, vpc('_ref', 1, 1, vpe)),
    % VPr = vp(Vr, vpe),
    findall(BV, member(bang(_, BV), Ann), Bs),
    check_banged_lhs(VPl, Bs, SS0, Ann, (*Vl := Vr)), % IO
    ( setof(PRA, VPRA^(VPRA=vp(Vr, PRA), member(s(VPRA, VPRA), SS0)), PRAs) ->
        true
    ;
        PRAs = []
    ),
    map(rvp_lvp(ref(T), Vl), PRAs, LVPs),
    map(self_alias, LVPs, SSS),
    map2(alias_var(Vr), PRAs, LVPs, SSR),
    % XX add s(VPl,VPl) in case rm_unshared_var_ref_aliases removes it below
    append(SSS, [s(VPl, VPl)|SSR], SSN),
    sort(SSN, SSNew),
    % print('assign PRAs SSR' - PRAs - SSR ), nl,
    % Sometimes we can remove old aliasing for VPl.
    % If some path for var on RHS aliases VPl then the previous version
    % of VPl is still "live" after the assignment so removing the old
    % aliasing may be unsound (XX check)
    ( aliases(SS0, VPl, vp(Vr, _))
    ->
        % XX make this an option
        % writeln('  Warning: possibly cyclic term '(Vl := Vr)),
        SS1 = SS0
    ;
        % we can do a bit better than this - see test.pns
        var_ref_shared_vars(Vl, SS0, SVars),
        % XXX strengthen???
        rm_unshared_var_ref_aliases(Vl, SVars, SS0, SS1)
    ),
    sharing_union(SSNew, SS1, SSRHS),
    % now handle var paths which alias LVP
    var_ref_alias_vps(VPl, SS0, AVPs),
    add_sharing_for_lhs_aliases(VPl, LVPs, AVPs, [], SSNew2),
    sort(SSNew2, SSNew3),
    sharing_union(SSNew3, SSRHS, SS).
alias_stat(C-Ann, SS0, SS) :-
    C = var_stat(V),
    ( member(last_stat, Ann) ->
        alias_stat(eq_var(returnvar, V)-Ann, SS0, SS)
    ;
        SS = SS0
    ).
alias_stat(C-Ann, SS0, SS) :-
    C = cases(V, Cases),
    member(typed(T), Ann),
    map(alias_stat_case(V, T, SS0), Cases, SSs),
    foldr(ord_union, [], SSs, SS). % XX balanced fold is better
alias_stat(C-Ann, SS0, SS) :-
    C = eq_dc(V, DC, Arity, Args),
    ( Args = [] -> % optimise case for constants
        SS = SS0
    ;
        member(typed(T), Ann),
        map('X,vp(X,vpe)', Args, DCAs),
        type_struct(T, TDSum),
        % XX hmm can fail if prev type checking failed
        % maybe we should not attempt sharing analysis if type checking
        % fails
        alias_stat_dc(V, TDSum, DC, Arity, 1, DCAs, SS0, SSN),
        sort(SSN, SSNew),
        sharing_union(SSNew, SS0, SS)
    ).
alias_stat(C-Ann, SS0, SS) :-
    C = eq_app(V, Fn, Args),
    % we are applying a variable which might be a closure.  We don't
    % know if returns a closure or not (see note in eq_sapp case)
    alias_stat_app(V, Fn, Args, Ann, SS0, SSN),
    length(Args, Arity),
    renumbered_closure_arg_sharing(Arity, Fn, V, SS0, SSN3),
    sort(SSN3, SSN4),
    sharing_union(SSN4, SSN, SSN1),
    sharing_union(SSN1, SS0, SS).
alias_stat(C-Ann, SS0, SS) :-
    C = eq_sapp(V, Fn, Args),
    % known saturated app: currently we only get this for known fns (not
    % vars which might be closures), so its a bit simpler.  Potentially
    % type analysis could pick up some cases where applications of vars
    % are known to be saturated (this would result in more efficient
    % compiled code).  If so, we may need a more general case here.
    alias_stat_app(V, Fn, Args, Ann, SS0, SSN),
    sharing_union(SSN, SS0, SS).
alias_stat(C-Ann, SS0, SS) :-
    C = eq_papp(V, Fn, Args),
    % (currently) known fn without enough args
    % no args -> no sharing (should use eq_var for such code??)
    % currently we don't allow nullary fns - they must have an arg, eg
    % void
    ( Args = [] ->
        SS = SS0
    % explicit calls to 'closure' are always partial apps; they are
    % in postconditions (+ pre sometimes), mostly implicit in src
    % code but describe all possible closure sharing
    ; Fn = closure ->
        length(Args, Arity),
        add_closure_arg_sharing(Arity, V, Args, SS0, SSN1),
        sort(SSN1, SSN2),
        sharing_union(SSN2, SS0, SS)
    ;
        alias_stat_app(V, Fn, Args, Ann, SS0, SSN),
        sharing_union(SSN, SS0, SS)
    ).

% case for application of fns/vars with args - return new sharing.
% Fn can be a constant or a variable.
alias_stat_app(V, Fn, Args, Ann, SS0, SSN) :-
    member(typed_rhs(RType), Ann),
    length(Args, Arity),
    LVP = vp(V, vpe),
    map('X,vp(X,vpe)', Args, AVPs),
    findall(BV, member(bang(_, BV), Ann), Bs),
    arrow_to_sharing_dus(Arity, RType, RFAs, Pre, APost, DUs, _, RWIs1, WOIs1),
    RFAs = [R|FAs],
    % we only need to keep sharing info for result and DU args
    % (including implicit ones)
    append([WOIs1, RWIs1, DUs], AllDUs1),
    filter_sharing_member(APost, [R|AllDUs1], Postcond),
    % we need to rename the result + formal args (RFAs) as LVP,
    % closure args (if needed) and Args (and extra formal args are not
    % needed, should be filtered out above and rename_sharing would drop
    % them anyway)
    % Eg, for arity 6 fn with 2 cl args supplied previously and 2 args
    % in application we have [Res,CLA4,CLA3,Arg1,Arg2]
    % Note numbering of closure args - Arg2 will become CLA1 of the
    % result
    RType = arrow(_, _, _, _, _, _, _, CLATs, ROIs, RWIs, WOIs),
    map('X,vp(X,vpe)', ROIs, ROVPs),
    map('X,vp(X,vpe)', RWIs, RWVPs),
    map('X,vp(X,vpe)', WOIs, WOVPs),
    length(CLATs, NCL),
    CLMin is Arity + 1,
    CLMax is CLMin + NCL - 1,
    mk_closure_var_paths(CLMin, CLMax, V, CLFnPs, _SSSC),
%     length(RFAs, NRFA),
%     ND is NRFA - 1 - Arity - NCL,
%     length(Dummies, ND), % need at least ND dummies; could have more
%     map0(=(vp('_dummy',vpe)), Dummies),
    % append([[LVP], CLFnPs, AVPs], ResArgs),
    append(CLFnPs, AVPs, AArgs),
    % rename_sharing ignores sharing between vars which are not renamed
    % so we have to explicitly include implicit args, which are renamed
    % to themselves (XX maybe rethink this)
    append([FAs, ROIs, RWIs], FAs1),
    append([AArgs, ROVPs, RWVPs], AArgs1),
    rename_sharing(Pre, FAs1, AArgs1, PreSS),
    sort(PreSS, PreSS1),
    rename_vars(DUs, FAs, AArgs, DUVs),
    append(RWVPs, DUVs, AllDUs),
    check_banged(Bs, AllDUs, SS0, Ann, (LVP = app(Fn, AVPs))), % IO
    % we include abstract with var for type so it matches any type
    append([[vp(abstract(_),vpe)], ROVPs, RWVPs, AVPs], AllVPs),
    (   member(S, SS0),
        S = s(SVP1, SVP2),
        SVP1 \= SVP2, % ignore self-sharing
        pair_in_var_list(S, AllVPs), % note result of fn can't be in precond
        % we generalise abstract so any type/path can match
        gen_abstract(SVP1, SVP3),
        gen_abstract(SVP2, SVP4),
        \+ member(s(SVP3, SVP4), PreSS1),
        print('Error: precondition violation:'(app(Fn, AVPs), S)),
        nl,
        write_src(Ann),
        fail
    ;
        true
    ),
    % have to also include result + wo args to rename postcond
    append([[R], WOIs, FAs1], RFAs1),
    append([[LVP], WOVPs, AArgs1], ResAArgs1),
    rename_sharing(Postcond, RFAs1, ResAArgs1, PostSS),
    % XXX best delete sharing pairs which include paths
    % of pure args which don't exist in SS0
    % filter_sharing_nopath(PostSS, SS0, DUs, PostSS1),
    sort(PostSS, PostSS1),
    % preconds for mutable args are added with postcond
    % (XX could get union of pre and post then call filter_sharing_member
    % as above - a bit simpler)
    filter_sharing_member(PreSS1, DUs, PreSS2),
    % Note: no transitivity used for pre+post
    ord_union(PostSS1, PreSS2, SSN1),
    % add self-sharing for WO implicit args
    map(nfdec_struct, WOIs, WOTs),
    map2(type_var_self_share, WOTs, WOIs, WOSSs),
    append(WOSSs, WOSS),
    sort(WOSS, WOSS1),
    ord_union(SSN1, WOSS1, SSN).

% generalise var paths for abstract so any type/path can match
gen_abstract(vp(V, P), vp(V1, P1)) :-
    ( V = abstract(_) ->
        V1 = abstract(_)
        % P1 = _
    ;
        V1 = V,
        P1 = P
    ).

% find any previous closure args for Fn and add closure arg sharing 
% for new var V (need to add Arity to the arg number)
renumbered_closure_arg_sharing(Arity, Fn, V, SS0, SSN) :-
    findall(FnP,
            (var_path_shared(SS0, vp(Fn, vpe), FnP),
            FnP = vpc(cla(_), _, _, _)),
        FnPs),
    map(renumbered_closure_arg_sharing1(Arity, V, Fn), FnPs, SSNPs),
    append(SSNPs, SSN).

% as above for single existing cla path of Fn
% returns self-sharing also (in list of length 2)
renumbered_closure_arg_sharing1(Arity, V, Fn, FnP, [S, SSelf]) :-
    FnP = vpc(cla(N), _, _, P), 
    N1 is N + Arity,
    mk_alias_pair(vp(V, vpc(cla(N1), 1, 1, P)), vp(Fn, FnP), S),
    self_alias(vp(V, vpc(cla(N1), 1, 1, P)), SSelf).

% add closure sharing for each of list of args, cl arg numbers
% descending
add_closure_arg_sharing(_, _, [], _, []).
add_closure_arg_sharing(N, V, [A|As], SS0, SSN) :-
    AVP = vp(A ,vpe),
    % we always have a self alias for this arg and empty path
    self_alias(vp(V, vpc(cla(N), 1, 1, vpe)), SSelf),
    findall(AP, var_path_shared(SS0, AVP, AP), APs),
    map(cla_path(V, N), APs, LVPs),
    map(self_alias, LVPs, SSS),
    map2(alias_var(A), APs, LVPs, SSA),
    N1 is N - 1,
    add_closure_arg_sharing(N1, V, As, SS0, SSN1),
    append([[SSelf|SSS], SSA, SSN1], SSN). % YY could make it tail recursive

% make closure var paths from M down to N + self-sharing pairs
mk_closure_var_paths(N, M, V, VPs, SS) :-
    ( N =< M ->
        M1 is M - 1,
        VP = vp(V, vpc(cla(M), 1, 1, vpe)),
        self_alias(VP, S),
        SS = [S|SS1],
        VPs = [VP|VPs1],
        mk_closure_var_paths(N, M1, V, VPs1, SS1)
    ;
        VPs = [],
        SS = []
    ).

% construct closure arg path
cla_path(V, N, P, vp(V,vpc(cla(N),1,1,P))).

% for assignment, convert path for RHS to var path for LHS
rvp_lvp(T, Vl, RP, vp(Vl, LP)) :-
    % avoid repeated solutions
    once(trunc_type_path(T, vpc('_ref', 1, 1, RP), LP)).

% make self-alias
self_alias(VP, s(VP, VP)).

% make alias pair from var, path, and var path
alias_var(Vr, Pr, LVP, S) :-
    mk_alias_pair(LVP, vp(Vr, Pr), S).

% given ancestor type, remove ref() wrapper from type or replace
% ref_anc(2) by ancestor
strip_ref_type(_, ref(_, T), T).
strip_ref_type(Anc, ref_anc(2), Anc).

% alias_stat for (possibly deref) var equality
alias_stat_veq(VPl, VPr, Ann, SS0, SS) :-
    member(typed(T), Ann),
    type_struct(T, Sum),
    % dataflow a bit tricky here - SSN filled in later
    ( VPl = vp(_, vpc('_ref', 1, 1, _)) ->
        type_struct(ref(T), LSum),
        mk_alias_pair(VPl, VPl, S), % add self-alias if lhs=ref
        SSN1 = [S|SSN]
    ;
        LSum = Sum,
        SSN1 = SSN
    ),
    ( VPr = vp(abstract(TA), vpe) ->
        % for abstract sharing, find all paths for the type (we assume
        % each component of abstract exists) then create all the sharing
        % pairs (that includes self sharing for abstract)
        type_paths(TA, RPs),
        rpath_aliases(RPs, VPr, LSum, VPl, SSN)
    ;
        findall(RP, var_path_shared(SS0, VPr, RP), RPs),
        rpath_aliases(RPs, VPr, LSum, VPl, SSN)
    ),
    sort(SSN1, SSNew),
    sharing_union(SSNew, SS0, SS).

% given path and type, compute type of subterms corresponding to path
path_type_map(vpe, T, T).
path_type_map(vpc(DC, _Arity, Arg, Path), T0, T) :-
    ( T0 = ref(T1) ->
        path_type_map(Path, T1, T)
    ; tdef(T0, Def0) ->
        member(dcons(DC, TArgs), Def0),
        % length(TArgs, Arity), % not needed?
        nth1(Arg, TArgs, T1),
        Path = vpc('_ref', _, _, Path1), % will always be a ref in path
        path_type_map(Path1, T1, T)
    ;
        % arrow types don't appear in tdef/2 and we need a special case
        % here to deal with them, otherwise sharing with abstract breaks
        % with higher order code.  We fudge things here by just saying
        % the type is void (so abstract(void) is what we use for sharing
        % with closure arguments)
        T0 = arrow(_,_,_,_,_,_,_,_,_,_,_),
        % DC = cla(N)
        T = void
    ).

% from sharing set, find all path suffixes for a given var path
% assumes self-sharing
var_path_shared(Ss, vp(V, VP), PSuff) :-
    member(s(VP1, VP2), Ss),
    VP1 = vp(V, PAll),
    VP2 = vp(V, _), % just consider at self-sharing pairs
    app_vpc(VP, PSuff, PAll).

% from (rhs) path suffixes and vars, construct share pairs
% (between lhs and rhs components, self-sharing for lhs and, if rhs is
% abstract/1 selfsharing for that also)
% We pass in type for LHS to filter and truncate paths as needed
% and also for fixing the type for abstract/1
% We use abstract(T) as a variable name, where T is the type of the
% component of the abstract variable that could be shared.  eg
% abstract(int) is  used as a fake variable that may share with any
% int component of an abstract var.
rpath_aliases([], _, _, _, []).
rpath_aliases([P|Ps], VPr, LSum, VPl, Ss) :-
    VPr = vp(Vr, Pr),
    VPl = vp(Vl, Pl),
    app_vpc(Pl, P, Pl1),
    app_vpc(Pr, P, Pr1),
    ( trunc_type_path_sum(LSum, Pl1, N) ->
        vpc_drop_last(N, Pl1, Pl2),
        % for abstract we need to fix the type and include
        % self-aliasing for abstract of that type
        ( Vr = abstract(T) ->
            path_type_map(Pr1, T, T1),
            Vr1 = abstract(T1),
            mk_alias_pair(vp(Vr1, vpe), vp(Vr1, vpe), SSSAS),
            Pr2 = vpe,
            Ss = [SSSAS, S1, S2|Ss1]
        ;
            Pr2 = Pr1,
            Vr1 = Vr,
            Ss = [S1, S2|Ss1]
        ),
        mk_alias_pair(vp(Vl, Pl2), vp(Vr1, Pr2), S1),
        mk_alias_pair(vp(Vl, Pl2), vp(Vl, Pl2), S2) % self-alias
    ;
        Ss = Ss1
    ),
    rpath_aliases(Ps, VPr, LSum, VPl, Ss1).

'X,vp(X,vpe)'(X,vp(X,vpe)).

% should be in a lib, implemented more efficiently
variant(L, R) :-
    subsumes_chk(L, R),
    subsumes_chk(R, L).
    % subsumes_chk is the name in older versions
    % subsumes_term(L, R),
    % subsumes_term(R, L).

% check pre and postconds etc for expected/given HO types:
% expected (LHS) should be "weaker"/less general
% We do a quick check for ~equality before the hard core stuff
check_ho_types(Anns, RHS, LT, RT) :-
    ( variant(LT, RT) ->
        true
    ;
        check_ho_types1(Anns, RHS, LT, RT)
    ).

% As above without top level check
check_ho_types1(Anns, RHS, LT, RT) :-
    ( (var(LT) ; var(RT)) ->
        true
    ; RT = arrow(_, _, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) ->
        check_ho_types_arrow(Anns, RHS, LT, RT)
    ;
        LT =.. [T|LAs],
        RT =.. [T|RAs], % should be same function symbol
        map(check_ho_types1(Anns, RHS), LAs, RAs)
    ).

% as above for arrow types
% XXX what happens when we have closure args of imcompatible types?
% XXXX what about implicit args: should check them + use them in
% renaming
% T1 as general as T2 if WOIs1 = WOIs2, RWIs1 >= RWIs2,
% ROIs1+RWIs1 >= ROIs2
check_ho_types_arrow(Anns, RHS, LType, RType) :-
    LType = arrow(LTTL, LTTR, LTBVs, _, _, _, _, _, _, _, _),
    RType = arrow(RTTL, RTTR, RTBVs, _, _, _, _, _, _, _, _),
    % we need a "sufficiently long" list of formal parameters
    % to rename the vars in L and R pre/postconds to so we can compare
    % the sets
    % XXX fix this using max arity
    RArgs = [result,a0,a1,a2,a3,a4,a5,a6,a7,a8,a9,b0,b1,b2,b3,b4,b5,b6,b7,b8,b9],
    map('X,vp(X,vpe)', RArgs, ResArgs),
    % We pick the max possible arity for the type to check if
    % saturated application has compatible pre/post conditions
    arrow_num(LType, Arity),
    arrow_to_sharing_dus(Arity, LType, LFAs, LPre, LPost, _LDUs, _, _, _),
    % XXXX need to include implicit args for renaming
    % see alias_fn
    rename_sharing(LPre, LFAs, ResArgs, LPreSS),
    rename_sharing(LPost, LFAs, ResArgs, LPostSS),
    sort(LPreSS, LPreSS1),
    sort(LPostSS, LPostSS1),
    arrow_to_sharing_dus(Arity, RType, RFAs, RPre, RPost, _RDUs, _, _, _),
    % XXXX need to include implicit args for renaming
    % see alias_fn
    rename_sharing(RPre, RFAs, ResArgs, RPreSS),
    rename_sharing(RPost, RFAs, ResArgs, RPostSS),
    sort(RPreSS, RPreSS1),
    sort(RPostSS, RPostSS1),
    % LType = arrow(_, _, _, _, _, SrcPre, SrcPost, _, _ROIs, _RWIs,
    % _WOIs),
    % ( ord_subset(LPreSS1, RPreSS1) -> % NQR
    % need to check subset but also take account of the fact that where
    % closure args are not specified, any sharing is allowed in precond
    % (can we have different types for closure args; if so ...? XXX)
    % We want to allow/ignore sharing of vars in LPreSS1 which don't
    % occur at all in RPreSS1, as these must be additional closure
    % arguments made explicit in L but not R.  See maybenot1 example
    (   member(SP, LPreSS1),
        \+ member(SP, RPreSS1),
        % above checks "not subset", now we ignore L-only sharing
        % write_src(Anns),
        % print(SP), nl, print(LPreSS1), nl, print(RPreSS1),nl,
        % writeln(LType), writeln(RType),
        SP = s(VPC1, VPC2),
        VPC1 \= VPC2,       % ignore self sharing for a start
        (   VPC1 = vp(SVar, _)
        ;
            VPC2 = vp(SVar, _)
        ),
        % a var sharing with abstract in L is an error if it shares
        % with anything in R (eg self)
        SVar \= abstract(_),
        once(
            member(s(vp(SVar, _), _), RPreSS1)
        ;
            member(s(_, vp(SVar, _)), RPreSS1)
        )
    ->
        NErr = 1,
        print('Error: incompatible precondition for '(RHS)), nl,
        print('  type is  '(RType)), nl,
        % print('  expected precondition '(SrcPre)), nl
        print('  expected '(LType)), nl,
        write_src(Anns)
        % , print((RFAs,LFAs)),nl, print(RPre), nl, print(LPre), nl
    ;
        NErr = 0
    ),
    ( ord_subset(RPostSS1, LPostSS1) ->
        NErr1 = NErr
    ;
        NErr1 is NErr + 1,
        print('Error: incompatible postcondition for '(RHS)), nl,
        print('  type is  '(RType)), nl,
        % print('  expected postcondition '(SrcPost)), nl
        print('  expected '(LType)), nl,
        write_src(Anns)
    ),
    % check mutable args: R should be subset of L
    % XXX need to rename first???
    ( member(BV, RTBVs), \+ member(BV, LTBVs) ->
        NErr2 is NErr1 + 1,
        print('Error: incompatible mutable argument '(RHS, BV)), nl,
        print('  type is  '(RType)), nl,
        print('  expected '(LType)), nl,
        write_src(Anns)
    ;
         NErr2 = NErr1
    ),
    % we avoid recursive checking if top level is wrong, to
    % reduce multiple similar error messages (especially for LTTR)
    ( NErr2 =:= 0 ->
        check_ho_types1(Anns, RHS, LTTR, RTTR),
        check_ho_types1(Anns, RHS, RTTL, LTTL)
    ;
        true
    ).

%%%%%%
% XXX add case_def handling
% case var of ... dcons(...) ->
% We know the data constructor for this var, so we filter out any
% other data constructors for this var from the current alias set to get
% new set.  Also need to add aliases for paths within var + args of
% data constructor
% Best use var path rather than var?
% Can we do the following at some stage?: if we have a var xs which
% is (x:xs1) and x is true and xs is [], all the aliasing of *xs* should
% be deleted (x and xs1 should be a var path starting with x rather than
% separarate vars, maybe).
% Worth looking at some examples to consider precision XX
% XXXX add stuff to handle cyclic terms + ??sharing between args
alias_stat_case(Var, T, SS0, case_dc(DC, Arity, As, S), SS) :-
    filter(alias_var_dcons_ok(Var, DC, Arity), SS0, SS1),
    type_struct(T, TS),
    TS = sum(_, Ps),
    member(prod(DC, Arity, Sums), Ps),
    % xxx(_),
    eq_case_args(As, Sums, TS, 1, Var, DC, Arity, SS0, SSN),
    sort(SSN, SSN1),
    sharing_union(SSN1, SS1, SS6),
    alias_stat(S, SS6, SS).

% 'X,var(X)'(X,var(X)).
% 'X,var(X)'(X,vp(X,vpc('_ref',1,1,vpe))).

% given args, arg num and var path + data constructor/arity from case,
% create alias pairs for var components and args (which must be *var)
eq_case_args([], _, _, _, _, _, _, _, []).
eq_case_args([Vr|As], [Sum|Sums], LSum, A, Vl, DC, Arity, SS0, SSN) :-
    % case is called with a top level type
    % TS=sum(_,[prod([Sum|Sums])...])
    % and the case args have the type one level down (ie, Sum).
    % They must be a reference to the top level, ref_anc(2), or a
    % reference to another type, ref(...).
    (   Sum = ref(RTN1, _Sum1),
        % need type_struct call to get ref_anc right
        type_struct(RTN1, RSum)
    ;
        Sum = ref_anc(2),
        LSum = sum(TSN, _), % extract parent info to construct arg type
        RSum = ref(ref(TSN), LSum)
    ),
    % we may also need to fold path for Vl
    Pl1 = vpc(DC, Arity, A, vpc('_ref', 1, 1, vpe)),
    ( trunc_type_path_sum(LSum, Pl1, N) ->
        vpc_drop_last(N, Pl1, Pl2)
    ;
        writeln('Huh? trunc_type_path_sum failed in eq_case_args'),
        Pl2 = Pl1
    ),
    VPl = vp(Vl, Pl2),
    VPr = vp(Vr, vpc('_ref', 1, 1, vpe)),
    findall(LP, var_path_shared(SS0, VPl, LP), LPs),
    % could move this earlier
    ( LPs = [] ->
        writeln('  Warning: unreachable case:'(DC/Arity))
    ;
        true
    ),
    mk_alias_pair(VPr, VPr, S), % self-alias
    rpath_aliases(LPs, VPl, RSum, VPr, SSN1),
    append(SSN1, [S|SSN2], SSN),
    A1 is A + 1,
    eq_case_args(As, Sums, LSum, A1, Vl, DC, Arity, SS0, SSN2).

% eq_dc handling
% XXXX do we miss adding sharing between different paths for
% Vl if different VPr's share???
% YES- BUG, eg see sa(*xp=1; p=t2(xp,xp))
alias_stat_dc(_, _, _, _, _, [], _, []).
alias_stat_dc(Vl, LSum, DC, Arity, A, [VPr|Args], SS0, SSN) :-
    findall(RP, var_path_shared(SS0, VPr, RP), RPs),
    Pl1 = vpc(DC, Arity, A, vpc('_ref', 1, 1, vpe)),
    ( trunc_type_path_sum(LSum, Pl1, N) ->
        vpc_drop_last(N, Pl1, Pl2)
    ;
        writeln('Huh? trunc_type_path_sum failed in alias_stat_dc'),
        Pl2 = Pl1
    ),
    VPl = vp(Vl, Pl2),
    mk_alias_pair(VPl, VPl, S), % self-alias
    rpath_aliases(RPs, VPr, LSum, VPl, SSN1),
    append(SSN1, [S|SSN2], SSN),
    A1 is A + 1,
    alias_stat_dc(Vl, LSum, DC, Arity, A1, Args, SS0, SSN2).

%%%%%%
% Overall handling of function definitions
% XX failure driven loop...
alias_fn(Fn) :-
    writeln('    sharing analysis of '(Fn)),
    nfdec_struct(Fn, T),
    func_arity(Fn, Arity),
    arrow_to_sharing_dus(Arity, T, RFAs, Precond, Postcond, BArgs, ROIs, RWIs, WOIs),
    fn_def_struct(Fn, Args, Stat),
    %
    % check all args which are banged in definition are banged in
    % declaration XX could delete if types are annotated with purity
    banged_vars(Stat, DUs),
    map('X,vp(X,vpe)', AVs, Args),
    sort(AVs, SArgs),
    ord_intersection(DUs, SArgs, DUArgs),
    sort(BArgs, SBArgs),
    ord_subtract(DUArgs, SBArgs, NDs),
    ( NDs = [] ->
        true
    ;
        writeln('Error: argument(s) should be declared mutable: '(NDs))
    ),
    ord_intersection(DUs, ROIs, DUROIs),
    ( DUROIs = [] ->
        true
    ;
        writeln('Error: implicit "ro" argument(s) should be rw: '(DUROIs))
    ),
    (   (   member(IV, RWIs)
        ;
            member(IV, WOIs)
        ),
        \+ mutable_global(IV),
        writeln('Error: implicit argument not declared mutable: '(IV)),
        fail
    ;
        true
    ),
    RFAs = [R|FAs],
    map('X,vp(X,vpe)', ROIs, ROVPs),
    map('X,vp(X,vpe)', RWIs, RWVPs),
    map('X,vp(X,vpe)', WOIs, WOVPs),
    append([FAs, ROIs, RWIs], FAs1),
    append([Args, ROVPs, RWVPs], Args1),
    % we include implicit args for renaming
    rename_sharing(Precond, FAs1, Args1, PreSS),
    % we include implicit args for renaming
    append([[R], WOIs, FAs1], RFAs1),
    append([[vp(returnvar, vpe)], WOVPs, Args1], ResArgs1),
    % rename_sharing(Postcond, RFAs1, ResAArgs1, PostSS),
    rename_sharing(Postcond, RFAs1, ResArgs1, PostSS),
    sort(PostSS, PostSS1),
    % extract types of args so we can init self-sharing
    nfdec_struct(Fn, TFn), % do we need to call this again?? YY
    smash_type_params(TFn),
    extract_ret_type(Arity, TFn, TFArgs, _TFR),
    append(ROIs, RWIs, RIs),
    map(nfdec_struct, RIs, RITs),
    append(RITs, TFArgs, AllArgTs),
    append(RIs, AVs, AllAVs),
    map2(type_var_self_share, AllArgTs, AllAVs, SSelfs),
    append([PreSS|SSelfs], SSI1),
    sort(SSI1, SSI2),
    % Note: no transitivity here
    ord_union(PostSS1, SSI2, PostSS2),
    % writeln(Stat),
    % write('checking...'), nl,
    % print(SSI2), nl,
    % append([ROIs, RWIs, WOIs], Is),
    % map('X,vp(X,vpe)', Is, IPs),
    % append(IPs, ResArgs, AllResArgs),
    ( alias_stat(Stat, SSI2, SS) ->
        % need to check for sharing between args+result which is not
        % declared in postcondition
        % also need to check for state vars which are introduced locally by
        % calling a WO function sharing with args+result; currently we
        % over-approximate by considering all state vars which are not
        % implicitly returned XXX NQR if we have local var with the same
        % name (should warn against this?)
        findall(SV, (mutable_global(SV),
                    \+ member(SV, RFAs1)
                    ), SVs),
        member(S, SS),
        S = s(VP1, VP2),
        VP1 = vp(V1, _),
        VP2 = vp(V2, _),
        V1 \= V2,   % XX ignore self aliasing - should include later?
        ( memberchk(vp(V1, _), ResArgs1) ->
            ( memberchk(vp(V2, _), ResArgs1) ->
                \+ member(S, PostSS2),
                print('Error: postcondition violated:'(Fn, VP1, VP2)),
                nl
            ;
                memberchk(V2, SVs),
                print('Error: illegal post-sharing with state variable:'(Fn, VP1, VP2)),
                nl
            )
        ;
            memberchk(vp(V2, _), ResArgs1),
            memberchk(V1, SVs),
            print('Error: illegal post-sharing with state variable:'(Fn, VP1, VP2)),
            nl
        )
    ;
        write('Oops! alias_stat failed :-('),
        nl
    ),
    fail.
alias_fn(_).

% get banged vars in stat
banged_vars(S, Vs) :-
    banged_vars_1(S, [], Vs1),
    sort(Vs1, Vs). % remove duplicates

% as above with accumulator
banged_vars_1(C-Ann, Vs0, Vs) :-
    ( C = seq(S1, S2) ->
        banged_vars_1(S1, Vs0, Vs1),
        banged_vars_1(S2, Vs1, Vs2)
    ;
        C = cases(_, Cs),
        foldr(banged_vars_case, Vs0, Cs, Vs2)
    ;
        add_banged_vars(Ann, Vs0, Vs2)
    ),
    add_banged_vars(Ann, Vs2, Vs).

% get banged vars from annotations and prepend to list
add_banged_vars(Ann, Vs0, Vs) :-
    findall(BV, member(bang(_, BV), Ann), BVs), % XX filter_map
    append(BVs, Vs0, Vs).

% as above for case (arg order for foldr)
banged_vars_case(Vs0, case_dc(_, _, _, S), Vs) :-
    banged_vars_1(S, Vs0, Vs).
banged_vars_case(Vs0, case_def(S), Vs) :-
    banged_vars_1(S, Vs0, Vs).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Pretty(er) output
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% XX may be a bit sus in parts, eg if we have name clashes between
% source code and some internal representation(?)
% XX should add pretty printing for arrow types
% Can also be confusing for debugging...
portray(X) :-
%    fail, % switch off pretty output
    d1(X).

d1(X) :-
    var(X),
    !,
    fail.
d1(dcons(Fn, As)) :-
    nonvar(Fn),
    T =.. [Fn|As],
    print(T).
d1(app(Fn, As)) :-
    nonvar(Fn),
    T =.. [Fn|As],
    print(T).
% d1(bang(S, V)) :-
%     print(S),
%     write(!),
%     print(V).
% d1(bang1(V)) :-
%     write(!),
%     print(V).
d1(deref(V)) :-
    write(*),
    print(V).
d1(var(V)) :-
    write(V).
d1(vp(V, VP)) :-
    write(V),
    print(VP).
d1(vpe).
d1(vpc(DC, Arity, N, VP)) :-
    write('.'),
    write(DC),
    ( Arity = 1 ->
        true
    ;
        write('/'),
        write(Arity),
        write('.'),
        write(N)
    ),
    print(VP).
d1(arrow(AT1, RT1, BVs, LA1s, R, Pre, Post, ETs, ROIs, RWIs, WOIs)) :-
    ( nonvar(AT1), AT1 = arrow(_, _, _, _, _, _, _, _, _, _, _) ->
        write('('),
        print(AT1),
        write(')')
    ;   
        print(AT1)
    ),
    write(' -> '),
    print(RT1),
    % only output sharing for innermost (this will work ok
    % for most cases, where innermost sharing is given and rest is
    % inferred)
    ( RT1 \= arrow(_, _, _, _, _, _, _, _, _, _, _) ->
        write(' sharing '),
        ( nonvar(LA1s) ->
            F =.. [f|LA1s],
            write(F = R),
            write(' pre '),
            print(Pre),
            write(' post '),
            print(Post)
        ;
            write('_')
        ),
        % print(' +'(BVs,ETs))
        print(' !'(BVs)),
        print(' imp'(ROIs, RWIs, WOIs)),
        print(' cl'(ETs))
    ;
        true
    ).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Other stuff...
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% stuff which should be in libraries, and related

% convert from (a,b,c) to [a,b,c] etc
csv_list(Vc, Vs) :-
    (Vc = (V, Vc1) ->
        Vs = [V|Vs1],
        csv_list(Vc1, Vs1)
    ;
        Vs = [Vc]
    ).

filter(_P, [], []).
filter(P, [A0|As0], As) :-
        (call(P, A0) ->
                As = [A0|As1]
        ;
                As = As1
        ),
        filter(P, As0, As1).

filter_map(_P, [], []).
filter_map(P, [A0|As0], As) :-
        (call(P, A0, A1) ->
                As = [A1|As1]
        ;
                As = As1
        ),
        filter_map(P, As0, As1).

split(_P, [], [], []).
split(P, [A0|As0], As, Bs) :-
        (call(P, A0) ->
                As = [A0|As1],
                Bs1 = Bs
        ;
                Bs = [A0|Bs1],
                As = As1
        ),
        split(P, As0, As1, Bs1).

foldr(_, B, [], B).
foldr(F, B, [A|As], R) :-
    foldr(F, B, As, R1),
    call(F, A, R1, R).

foldl(_, B, [], B).
foldl(F, B, [A|As], R) :-
        call(F, B, A, B1),
        foldl(F, B1, As, R).

map(_F, [], []).
map(F, [A0|As0], [A|As]) :-
    call(F, A0, A),
    map(F, As0, As).

map2(_F, [], [], []).
% map2(_F, [_|_], [], []).
map2(F, [A0|As0], [A1|As1], [A|As]) :-
    call(F, A0, A1, A),
    map2(F, As0, As1, As).

map3(_F, [], [], [], []).
% map3(_F, [_|_], [], []). % ...
map3(F, [A0|As0], [A1|As1], [A|As], [B|Bs]) :-
    call(F, A0, A1, A, B),
    map3(F, As0, As1, As, Bs).

map_acc(_F, [], [], X, X).
map_acc(F, [A0|As0], [A|As], X0, X) :-
    call(F, A0, A, X0, X1),
    map_acc(F, As0, As, X1, X).

map0_acc(_F, [], X, X).
map0_acc(F, [A|As], X0, X) :-
    call(F, A, X0, X1),
    map0_acc(F, As, X1, X).

% unused??
map2_acc(_F, [], [], [], X, X).
% map2(_F, [_|_], [], []).
map2_acc(F, [A0|As0], [A1|As1], [A|As], X0, X) :-
    call(F, A0, A1, A, X0, X1),
    map2_acc(F, As0, As1, As, X1, X).

map0(_F, []).
map0(F, [A0|As0]) :-
    call(F, A0),
    map0(F, As0).

map0_comma(_F, []).
map0_comma(F, [A0]) :-
    call(F, A0).
map0_comma(F, [A0|As0]) :-
    As0 = [_|_],
    call(F, A0),
    write(', '),
    map0_comma(F, As0).

% in library somewhere?  whats the name?
drop(0, As, As).
drop(N, [_|As], Bs) :-
    N > 0,
    N1 is N - 1,
    drop(N1, As, Bs).

% in library somewhere?  whats the name?
take(0, _, []).
take(N, [A|As], [A|Bs]) :-
    N > 0,
    N1 is N - 1,
    take(N1, As, Bs).

fst(A-_, A).

snd(_-A, A).

% should be in assoc library (arg order???)
% return value associated with key; insert if not there already
lookup_assoc(Key, Assoc, Value, NewAssoc) :-
    ( get_assoc(Key, Assoc, Value) ->
        NewAssoc = Assoc
    ;
        put_assoc(Key, Assoc, Value, NewAssoc)
    ).

% return value associated with key; insert var if not there already
% but print error (best pass in Anns for better msg)
lookup_old_assoc(Key, Assoc, Value, NewAssoc) :-
    ( get_assoc(Key, Assoc, Value) ->
        NewAssoc = Assoc
    ;
        writeln('Error: undefined variable '(Key)),
        put_assoc(Key, Assoc, Value, NewAssoc)
    ).

% dummy pred we can put a spy point on
xxx(_).

/*
sa(bool:: x = y).
sa(ref(bool):: x = y).
sa(bs:: *x = cons(a, nil); bs:: *x := cons(y, x)).

sa(pb:: *x = pair(true, false); pb:: *!y := *x; pb:: *!y := z !x).

sa(pb:: x = pair(true, false); cases pb::x of (case pair(*l,*r): bool:: *!y := true)).

sa(lp(x, y); lp(x,y)).

sa(ref(bs):: x = cordlist1(c,y) !c!y).
sa(ref(bs):: x = cordlist1(c,y) !c!y; ref(bs):: z= cordlist1(c,y) !c!y).

alias_fn(lastp, 1).
alias_fn(cordlist, 1).
alias_fn(cordlist1, 2).
alias_fn(eval, 1).
alias_fn(eval_whnf, 1).
alias_fn(deref, 1).

sa(bs:: l = cons(a, cons(b, l1))).
% below ok: a not modified by := desite being shared by (part of) l
sa(bs:: l=cons(a, nil); bs:: !l:=cons(a1, l)).
% below error: l modified by := since its shared by *p (exactly)
sa(bs:: *p=nil; bs:: l=cons(a, *p);  bs:: *!p:=nil).
% below ok: cons cell has a copy of *p - not aliased to *p
sa(bool:: *p=true; bs:: l=cons(*p, nil);  bs:: *!p:=false).
% below ok, even though b = *a doesn't keep track of value of a
% currently
sa(*a = just(true); b = *a; *!a := nothing).
% below error (assignment may modify b) if we don't keep track of value
% of a and do simple type folding.  The reason is b = *a is abstracted
% the same way as b = cons(true, *a) and *!a := nil is abstracted the
% same way as *lastp(a) := nil (or *&tail(*a) := nil in C)
sa(*a = cons(true,nil); b = *a; *!a := nil).

% precond violations:
sa((cb::c0=leaf(l); cb::c1=cord_app(c0,l))).
sa((cb::c1=cord_app(c0,l); cb::c2=cord_app(c1,l))).
sa(term:: t = u).


sa((cases cb:: x of (case leaf(*q): bool::b=b))).
sa((cases cb:: x of (case leaf(q): bool::b=b))).
sa((cases bs::x of (case cons(h,t): bool::b=b))).
sa((cases bs::x of (case cons(*h,*t): bool::b=b))).

sa((xs1 = cons(true, nil); xs2 = cons(true,xs1); cases xs2 of (case cons(*h,*t): true))).
sa((xs1 = cons(true, nil);cases xs1 of (case cons(*h,*t): true))).
sa((xs1 = nil;cases xs1 of (case cons(*h,*t): true))).
sa((x=nothing; cases x of (case nothing: true))).
sa((x=nothing; cases x of (case just(*b): true))).
sa((x=just(true); cases x of (case just(*b): true))).

% various cases (covers lots of things) using wam.pns
sa(bool:: aaa=b).
sa(bool:: aaa = *b).
sa(bool:: *aaa = b).
sa(bool:: *aaa = *b).
sa(ref(bool):: aaa=b).
sa(bool:: * (* (*aaa)) = * (* (*b))).
sa(bool:: * (* (*!aaa)) := * (* (*b))).
sa(ref(ref(ref(bool))):: aaa=b).
sa(terms:: cs = bbb).
sa(terms:: cs = cons(nv(f1,nil), bbb)).
sa(terms:: cs = cons(aaa, nil)).
sa((cases terms:: cs of (case cons(aaa, *bbb): terms:: *!bbb:=nil!cs!aaa))).
sa((cases terms:: cs of (case cons(aaa, bbb): terms:: cs=cs))).
sa(term::a=b).
sa(term::a=var(b)).
sa((cases term:: a of (case var(b): term::b=b))).
sa(term::a=nv(b,nil)).
sa((cases term:: a of (case nv(b, *ts): terms:: *!ts:=nil!a))).
sa(term::a=nv(*b,nil)).
sa((cases term:: a of (case nv(*b, *ts): terms:: *!ts:=nil!a))).
sa((cases term:: a of (case nv(*b, *ts): terms::ts=ts))).
sa((cases term:: a of (case nv(b, ts): terms::ts=ts))).
sa((cases term:: a of (case nv(*b, ts): terms::ts=ts))).
sa(t = nv(f,cons(a,as))).
sa(ts = cons(v, ts1)).
sa(t = nv(f,ts)).
sa(cases t of (case nv(*f, *ts): a=true)).


sa((cb:: t = branch(l, r))).
sa((cb:: t = branch(l, r) ; cases cb:: t of ( case branch(zl1, zr1): bool:: tmp = true))).
sa((bool:: *rt = true; ref(bool):: *rrt = rt; ref(ref(bool)):: rrt1 =
rrt; bool:: *rf = false; ref(bool):: *rrt := rf)).


listing(type_struct_c).
listing(nfdec_struct).
listing(fdef_struct).
listing(prog_dcons).
listing(teqdef).
listing(tdef).

comp(pbst).
comp(bst).
comp(cord).
comp(eval).
comp(wam).
comp(isort).

alias_fn(list_bst_du, 4).

% goals which distinguish between old sharing imp and new (with
% self-sharing to keep track of what paths are possible for each var
sa((ys=nil;b=true; xs=cons(b,ys))). % any sharing with ys?
sa((ys=nil;b=true; xs=cons(b,ys); *xsp = xs)). % any sharing with ys?
sa((ys=nil; *ysp=ys;b=true; xs=cons(b,ys))).
% some precision lost below since s(ysp.ref,ysp.ref) looks like spine of
% list exists, even though elements don't (would be better if we didn't
% recurse to root, or expanded one more level in type tree - rethink
% this with self-sharing scheme and flattening XX)
sa((ys=nil; *ysp=ys;b=true;ys1= *ysp; xs=cons(b,ys1))).
sa((ys=nil; *ysp=ys;b=true; xs=cons(b,ys); *ysp := xs)).
sa((ys=nil;b=true; xs=cons(b,ys); *xsp = xs; *xsp:=ys)).
sa(*b = nil;*b := cons(true,*b)).
sa(*b = cons(true,nil); *b := *b).

% illustrates some tricky things about arrow types - extra args, extra
% types, closure sharing in postconds...
canon_type_name((mb -> mb -> mb -> mb
    implicit rw io2, wo gv, rw io1, ro rg, rw io
    sharing f1(b1, b2,b3) = rb
    pre b1=b3
    post rb = b1), T), writeln(T).

% examples for sharing paper
san('sh.pns').
sa(ts = cons(rnode(2, cons(rnode(3,nil),nil)),nil)).
sa(t = rnode(2, cons(rnode(3,nil),nil))).
sa(t = rnode(2, nil);ts = cons(t, nil)).


san('testuf.pns').
san('eval.pns').
san('wam.pns').
san('isort.pns').
san('bst_poly.pns').
san('bst1.pns').
san('cord.pns').
san('cord_poly.pns').
san('ho.pns').
san('imp.pns').

san('bst.pns').

san('bst_a.pns').
san('test.pns').
san('tmp.pns').
san('pbst.pns').
san('p1bst.pns').

spy(alias_stat).
spy(in_as).
spy(xxx).
spy(arrow_to_sharing_dus).
/^alias_stat
[pawns].
[pawns,comp].
['../pawns.pl', '../comp.pl'].

prolog

spy(rm_unshared_var_ref_aliases).
sa(*zp = 42; *wp = 43;    *yp = zp;    *xp = yp;    *yp := wp).

retractall(tdef(T, D)), builtin_tdef(T, D), assert(tdef(T, D)), fail.
retractall(nfdec_struct(Fn1, T)), builtin_fdec((Fn :: ST)), fdec_fdec_struct(Fn, ST, Fn1, T), assert(nfdec_struct(Fn1, T)), fail.
retractall(func_arity(Fn, Arity)), builtin_func_arity(Fn, Arity), assert(func_arity(Fn, Arity)), fail.

% missing s(p.t2/2.1._ref._ref,p.t2/2.2._ref._ref) ???
sa(*xp=1; p=t2(xp,xp)).

alias_stat(eq_var(x,abstract(list(pair(int, int))))- [typed(list(pair(int, int)))], [], SS), print(SS), fail.

*/

x :- spy(xxx).
as :- spy(alias_stat).
ar :- spy(arrow_to_sharing_dus).
at :- spy(add_typed_anns).
t :- trace.
p :- [pawns].


