% *prototype* implementation of Pawns
% (Pointer Assignment With No Surprises)
% Reads Prolog-ish syntax, converts to internal form of "core" Pawns,
% does type analysis and sharing analysis then does simple translation to
% C + support for algebraic data types provided by the adtpp tool.
% 
% This file is too long and the structure within it is not understood -
% it should be broken up into separate modules etc...
% comp.pl has a bit of top level code and the translation to C+adtpp; the
% other 90% is here.

% XXX see Bugs file for more things to fix plus XXX here and in *.pns
% elsewhere (some may be fixed already; plus there are no doubt plenty of
% unknown bugs and limitations)

% XXX need to FIX sharing analysis for cases ++ (see paper)
% (sharing between different args of DC)

% XXX using data constructor as fn makes things go crazy
% map(t2, [true, false, true], Ps1); in duspec.pns

% XXX If reading input gets scrambled it seems an infinite loop is
% possible (duspec.pns)
% Error: undefined type ......
% Error: type error in var equality/assignment:(((p::ref(_134942)),(V4::list(_134446))))
%   source: *p=cons(abstract,nil) 

% ??? rethink operator precedence of implicit so (hopefully) we don't need
% t1 -> (t2 -> t3) implicit ...  See comments elsewhere (OK)

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
% type vars in the prototype. (casts not needed much now)

% XXX some hacking done related to name/2 etc due to the way string
% handling has changed in Prolog over the years.  Should just go with
% the modern way of doing things probably.

% Notes:
% State variables and higher order - clarification (probably not the best
% place to put this but it's better than nowhere - its's a bit tricky).
% If we call f::int -> int -> int implicit wo svwo, rw svrw with two
% arguments its all clear - svwo will get defined (so we must save the old
% value before this call end restore it before we return), svrw must be
% defined already and it may be used and modified.  However, what if f is
% called with just one argument? If it's defined with two arguments we just
% create a closure and nothing is done until we call the closure later (if at
% all). If f is defined with one argument and returns a closure, potentially
% it can do some things then more things are done when we call the closure
% later. For example, the first call may or may not define svwo and
% reads/updates svrw.
% See comments in canon_type_name for how this is handled - there is a
% default way of inheriting state vars from rightmost arrows to other
% arrows but it can be overridden by (nested) declarations of implicit
% args on multiple arrows.
% Do we need to include sharing info for implicit args in closures
% (thats what lead us down a rabbit hole...)? Implicit vars are not
% actually there but update of them will effectively change the value of
% the closure in some sense. However, when the closure is actually
% called it will have an ! annotation anyway and it should be clear it
% uses the current version of the state vars. Two questions:
% 1) Do we need extra explicit info such as sharing in postconditions?
% No - return type has implicit in it and that should be sufficient.
% 2) Do we need extra ! annotations for things like *!sv := val !closurefn
% (where closurefn is a closure that has sv implicit)?
% No again: ! on call to closurefn is sufficient.
% Note we *could* answer yes to these questions, making the source code
% a bit more explicit about things (and the compiler a bit more
% complicated).  With the current choice, programmers should be extra
% mindful when using closures that have implicit arguments and note that
% implicit arguments are not really passed around, they are basically
% global variables.  From the semantics point of view this may cause
% some complications.

% Processing pre/post-conditions.  These are processed with the same
% sharing analysis algorithm as for statements to compute the sharing sets
% for the condition.  We allow some more flexibility so we can have more
% concise description of sharing.  We allow redefinition of variables, eg
% x = y; x = z means x shares with y and sares with z.  It would be nice
% to allow abstract in arguments of data constructors, eg, x =
% cons(abstract, y) to say x is a list of things that share with abstract
% but generally this doesn't work. The abstract needs to be the same type
% as the list elements but before type checking the code is transformed to
% V1 = abstract; x = cons(V1, y) and the abstract has a polymorphic type
% (the same as V1) and when the cons is processed an instance of the type
% is used.  XXX maybe we could use a hack like that we use for assignment of
% variables of a polymorphic type to instantiate the type at this point?

% XXXX if c <= 0 then return(t) needs else (bst_count.pns)

% XXX probably should move info about types and abstract domain here also
% see "type representation for sharing analysis"

:- ensure_loaded(library(ordsets)).

% set up operators to enable OK syntax to be used (see *.pns)
% XX try to tweek these so we can declare vars locally with :: but no
% () (priority of :: should be low)
:- op(2, fx, ...).
:- op(4, xfy, (^)). % shouldn't break things; used for more precise DU 
:- op(7, fx, (!)).
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
:- op(1150, fx, (du_spec)).
:- op(1150, fx, (type)).
:- op(1150, fx, (renaming)).
:- op(1100, xfx, (with)).
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
    \+ state_var(Fn, _),
    alias_fn(Fn),
    fail.  
share_anal :-
    writeln('    Sharing analysis completed\n').

% read source file and
% assert everything XX (should pass it around as state).
input_file(File) :-
    retractall(du_spec(_, _)),
    retractall(imported(_)),
    retractall(prog_dcons(_)),
    retractall(c_fn_def(_, _)),
    retractall(extern_fn(_)),
    retractall(func_arity(_, _)),
    retractall(fdef_struct(_, _, _, _)),
    retractall(nfdec_struct(_, _)),
    retractall(nfdec_struct_inferred_post(_, _)),
    retractall(type_struct_c(_, _)),
    retractall(teqdef(_, _)),
    retractall(tdef(_, _)),
    retractall(state_var(_, _)),
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
        % These clauses have no body *except* for '_type_param', which
        % is fudged (see builtin_tdef).
        (   clause(builtin_tdef(T, D), TdefBody)
        ;
            member(tdef(T0,D0), As),
            canon_tdef(tdef(T0,D0), tdef(T,D)),
            TdefBody = true
        ),
        assert(tdef(T, D) :- TdefBody),
        % member(tdef(T1, _), TDs), % nondet
        % tdef_tdef_struct(TDs1, T1, type_struct_c(T1, S)),
        % assert(type_struct_c(T1, S)),
        fail
    ;
        % state var declarations - they look like function declarations
        % but must be processed first because when we process function
        % declarations we want to know about state vars
        Fn = (!_), % state var dec
        (   builtin_fdec((Fn :: ST)) % could separate builtin SV
        ;
            member((Fn :: ST), As)
        ),
        % state vars asserted in fdec_fdec_struct
        % XXX could restructure this a bit
        fdec_fdec_struct(Fn, ST, Fn1, T),
        assert(nfdec_struct(Fn1, T)),
        fail
    ;
        % function declarations
        (   builtin_fdec((Fn :: ST))
        ;
            member((Fn :: ST), As)
        ),
        Fn \= (!_), % not state var dec
        fdec_fdec_struct(Fn, ST, Fn1, T),
        % inferred postconditions are set aside for processing below
        (has_inferred_post(T) ->
            assert(nfdec_struct_inferred_post(Fn1, T))
        ;
            assert(nfdec_struct(Fn1, T))
        ),
        fail
    ;
        % replace "inferred" postconditions with function bodies
        nfdec_struct_inferred_post(Fn, T),
        ( member(fdef(PFH, PFB), As), functor(PFH, Fn, _) ->
            rename_inferred_postcond(T, PFH, PFB, T1),
            assert(nfdec_struct(Fn, T1))
        ;
            fail
        ),
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
% Renaming declarations are handled here, taking the declarations and
% function definitions and producing extra (renamed) function
% definitions.
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
    split(is_type_def, Ts3, TTDefs, Ts4),
    split(is_renaming_def, Ts4, TRDefs, Ts5),
    split(is_du_spec, Ts5, DUDefs, TOs),
    map0(do_du_spec, DUDefs),
    split(is_fn_dec, TOs, TFDecs, TFDefs),
    map(es_as_type, TTDefs, ATDefs),
    map(es_as_fdef, TFDefs, AFDefs),
    map(rename_fdefs(AFDefs), TRDefs, ARFDefss),
    append(TFDecs, AFDefs, As1),
    append(ARFDefss, ARFDefs),
    append(ARFDefs, As1, As2),
    append(ATDefs, As2, As).

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

% checks if term is a duspec def
% XXX more sanity checking
is_du_spec((du_spec _)).

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

% for duspec names/shorthands
:- dynamic((du_spec)/2).

% expand named duspecs (XXX currently top level only)
expand_du_spec(Name, DUS) :-
    ( du_spec(Name, DUS1) ->
        DUS1 \= Name, % XXX should have sanity checking of duspecs
        expand_du_spec(DUS1, DUS)
    ;
        Name =.. [F|DUS1],
        map(expand_du_spec, DUS1, DUS2),
        DUS =.. [F|DUS2]
    ).

% handle duspec naming
% (assumes list; XXX just comma separated would be nicer)
do_du_spec(du_spec(DUs)) :-
    member(Name = DUS, DUs),
    ( du_spec(Name, _) ->
        writeln('DU spec name repeated: '(Name))
    ;
        assert(du_spec(Name, DUS))
    ),
    fail.
do_du_spec(_).

% for imported things
:- dynamic(imported/1).

% checks if term is a type def
is_type_def((type _ = _)).
is_type_def((type _ ---> _)).

% checks if term is a fn dec
% XX fix if we tweek op priorities
is_fn_dec((_ :: _)).

% checks if term is a renaming dec
is_renaming_def((renaming _)).

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
        nl,
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
        nl,
        writeln('Error: malformed function type declaration:'(Fn0 :: T)),
        canon_type_name((void -> void
                    sharing f(v) = r pre nosharing post nosharing), I)
    ),
    % XXX add more sanity checking for duspec on state vars
    % Default duspec is ...!; outer ref added in other cases
    ( (Fn0 = (!Fn^DUS0), atom(Fn), DUS = ref(!/DUS0) ;
            Fn0 = (!Fn), atom(Fn), DUS = (...!)) ->
        expand_du_spec(DUS, DUS1),
        assert(state_var(Fn, DUS1)),
        ( I = ref(_) ->
            true
        ;
            nl,
            writeln('Error: mutable global must have ref type: '(Fn0 :: T))
        )
    ; atom(Fn0) ->
        Fn = Fn0
    ;
        nl,
        writeln('Error: malformed declaration:'(Fn0 :: T)),
        Fn = '_foobar'
    ).

% store mutable globals (state variables) + their duspecs
:- dynamic(state_var/2).

% renaming declaration handling:
% Given list of all functions and a renaming def, return a list of
% renamed functions
rename_fdefs(FDefs, Dec, RFdefs) :-
    ( Dec = (renaming REqc with WEqc) ->
        renaming_rhs_to_list(REqc, RPs),
        renaming_rhs_to_list(WEqc, WRPs),
        append(WRPs, RPs, AllRPs),
        map(find_and_rename(FDefs, AllRPs), RPs, RFdefs)
    ; Dec = (renaming REqc) ->
        renaming_rhs_to_list(REqc, RPs),
        map(find_and_rename(FDefs, RPs), RPs, RFdefs)
    ).

% convert RHS of renaming declaration to list of pairs
renaming_rhs_to_list(REqc, RPs) :-
    (REqc = (L = R, REqc1) ->
        RPs = [L-R|RPs1],
        renaming_rhs_to_list(REqc1, RPs1)
    ; REqc = (L = R) ->
        RPs = [L-R]
    ;
        nl,
        writeln('Error: malformed renaming declaration RHS:'(REqc)),
        RPs = []
    ).

% from list of function definitions and list of renaming pairs, create
% list of new renamed function definitions
% XXX should have more resilient error handling
find_and_rename(FDefs, AllRPs, _-OF, RFdef) :-
    (member(fdef(PFH, PFB), FDefs), functor(PFH, OF, _) ->
        rename_term(AllRPs, PFH, RPFH),
        rename_term(AllRPs, PFB, RPFB),
        RFdef = fdef(RPFH, RPFB)
    ;
        writeln('Error: no function definition to rename'(OF)),
        % XXX might cause failure later
        RFdef = fdef(dummy_renamed_function(v), v)
    ).

% replace function symbols in term using list of new-old pairs
% (pair order potentially counterintuitive)
rename_term(RPs, T0, T) :-
    functor(T0, F, N),
    (member(RF-F, RPs) ->
        true
    ;
        RF = F
    ),
    functor(T, RF, N),
    rename_term_args(RPs, N, T0, T).

% as above for args
rename_term_args(RPs, N, T0, T) :-
    ( N =< 0 ->
        true
    ;
        arg(N, T0, A0),
        arg(N, T, A),
        rename_term(RPs, A0, A),
        N1 is N - 1,
        rename_term_args(RPs, N1, T0, T)
    ).

% test if declared postcond of fn is "inferred"
% XXX NQR - should really check for inferred in Nth arrow, where there
% are N explicit arguments in the function definition. There really
% shouldn't be inferred anywhere else.
has_inferred_post(T) :-
    T = arrow(_, R, _, _, _, _, Post, _, _, _, _),
    ( var(Post) -> % needed for closure+apply hack with vars
        fail
    ; Post = inferred ->
        true
    ;
        has_inferred_post(R)
    ).

% replace inferred by renamed fn body
% XXX NQR, as above - we just replace the first inferred we see
replace_inferred(T0, FB, T) :-
    T0 = arrow(X1, R0, X2, X3, X4, X5, Post, X6, X7, X8, X9),
    ( Post = inferred -> 
        T = arrow(X1, R0, X2, X3, X4, X5, FB, X6, X7, X8, X9)
    ;
        T = arrow(X1, R, X2, X3, X4, X5, Post, X6, X7, X8, X9),
        replace_inferred(R0, FB, R)
    ).

% take type signature with "inferred" as postcondition and replace it
% with body of function definition, renamed so formal params of function
% are replaced by formal params in type definition; also need to
% replace return by assignment to result variable
% XXX map2 fails if sharing has wrong number of args ->
% ERROR: suspect definition:... (could give better msg)
rename_inferred_postcond(T0, FH, FB, T) :-
    FH =.. [_|FArgs],
    T0 = arrow(_, _, _, TArgs, TRes, _, _, _, _, _, _),
    map2(pair, TArgs, FArgs, Renames),
    % XXX we need to introduce var TRes into the postcondition code.
    % If that var name is used already it needs to be renamed, so we
    % pick a name that nobody would ever use... (yeah, right)
    %  Hey, we could always make renamedXYZZY a reserved word in the
    %  language definition
    rename_term([renamedXYZZY-TRes|Renames], FB, FB1),
    pstat_fix_return(FB1, TRes, FB2),
    replace_inferred(T0, FB2, T).

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
% XXXX currently it's assumed the arguments in FH are the same as the
% arguments in the pattern in the arrow type - should check/rename, otherwise
% we get the "banged" vars in the type being different from the intended
% banged vars in the code
fdef_fdef_struct1(FH, FB, fdef_struct(FName, FAs, Stat, VTm)) :-
    FH =.. [FName|FHAs],
    map(arg_fdefarg, FHAs, FAs),
    nfdec_struct(FName, TF),
    % we replace distinct type vars with distinct new ground
    % types for checking (in the type we use variables so we
    % can get instances of the type for calls)
    smash_type_params(TF),
    length(FHAs, Arity),
    extract_ret_type(Arity, TF, TFArgs, TFR),
    % [TFR|TFArgs] is expected types [returnvar|FHAs]
    ( TF = arrow(_, _, _, _, _, _, _, _, ROIs, RWDUIs, WOIs) ->
        map(strip_duspec, RWDUIs, RWIs),
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
    add_typed_anns(FB, S1, VTm1, VTm, [], PolyVs),
    % check implict wo vars are instantiated and have types
    % compatible with declarations (like := type check)
    ( TF = arrow(_, _, _, _, _, _, _, _, _, _, WOIs) ->
        globals_type_assoc(WOIs, VTmWO),
        (   gen_assoc(WOV, VTmWO, WOTl-_DF), % generate & test
            ( get_assoc(WOV, VTm, WOTr-def) ->
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
    findall(SV, state_var(SV, _), AllVs),
    % need to include mutable args also! XXX actually all args
    % type_to_banged(TF, BVs),
    append(FHAs, AllVs, AllVs1),
    sort(AllVs1, Vs1),
    % XPOLY From VTm we can determine all vars with polymorphic types
    % and add used_later everywhere so they have to be banged, even with
    % their last use (XXX a bit of overkill - really only needed if their
    % type is further instantiated in the last call and they share with
    % other vars)
    append(Vs1, PolyVs, Vs2),
    add_last_anns(S1, Stat, last(TFR), Vs2, _UVs, [], _IBVs).

% remove duspec annotation from var
strip_duspec(V^_, V).

% returns list of vars with polymorphic types
poly_vars(VTm, PolyVs) :-
    findall(PV, (
        gen_assoc(PV, VTm, PT),
        \+ once_fresh_var(PV), % ignore generated var names
        \+ ground(PT)
        ), PolyVs).

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

% call lookup_assoc given var-type pair; add def flag
unpair_lookup_assoc(V-T, VTm0, VTm) :-
    lookup_assoc(V, VTm0, T-def, VTm).

% given type, strip off outer Arity arrows to give type of each arg and
% return type of fn
extract_ret_type(A, T0, TAs, T) :-
    (A = 0 ->
        TAs = [],
        T = T0
    ; T0 = arrow(TA, T1, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) ->
        TAs = [TA|TAs1],
        A1 is A - 1,
        extract_ret_type(A1, T1, TAs1, T)
    ;
        writeln('Error: not enough arrows in type'(T0)),
        % XXX should pass in src for error message
        % may barf later
        TAs = [],
        T = T0
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
arrow_to_sharing_dus(Arity, T0, [R|FAs], PreSS, PostSS, BVs, ROIs, RWDUIs, WOIs) :-
    % type vars are replaced by _bot, because if a function returns
    % list(T), for example, there can be no elements T returned - it
    % must return an empty list.
    copy_term(T0, T),
    smash_type_vars(T),
    % we get the (arrow) type nested Arity arrows down - that has
    % the sharing/DU + implicit arg info we need + type of result TR
    extract_ret_type_arrow(Arity, T, _, TR, OA),
    OA = arrow(_, _, BVs, _, _, Pre, Post, _, ROIs, RWDUIs, WOIs),
    map(strip_duspec, RWDUIs, RWIs),
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
    % or abstract or ro/rw state var
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
    % We treat wo vars similarly
    map2(type_var_self_share, AllResArgTs, AllResFAs, RSelfss),
    append(RSelfss, RSelfs),
    % XXX if postconditions don't implicitly include sharing from precondition
    % the next line is appropriate. This potentially allows a bit more
    % precision at the cost of more verbose postconditions, though only
    % when we smash data structure to reduce sharing, which is uncommon.
    % append(RSelfs, SSS2, SSS3),
    append(RSelfs, PreSS, SSS3),
    sort(SSS3, SSS4),
    % SSS4 = SSS2, % appropriate if we don't want self share for result
    cond_share(VTm1, Post, SSS4, PostSS1),
    % we delete all share pairs involving anything but an arg var,
    % the result var or abstract or wo/rw state var
    filter_sharing_both_member(PostSS1, AllResFAs, PostSS).

% Currently use upper case (Prolog vars) for type vars and sometimes we
% want a ground type that has the desired result. Here we smash any vars
% with type _bot, which has no components for sharing (if something is
% of list(T) where T is a var, for example, it can't have any components
% of type T (it must be nil), so list(_bot) has the same set of
% components.  We have a special case for pre/post conditions so we can
% have more type vars around without eliminating paths. XXXXB
% Old version used ref(void) so there was a single component for this
% (and more for data constructors around it).
% This caused bogus precondition violations if we have a
% function that returns something with a polymorphic type, eg
% l = return_nil(void); accept_list_of_int(l)
% (worse, it caused failure of alias_stat on occasion!)
smash_type_vars(T) :-
    ( var(T) ->
        % T = ref(void)
        ( checking_pre_post ->
            T = ref('_bot')
        ;
            T = '_bot'
        )
    ; T = arrow(_, _, _, _, _, _, _, _, _, _, Is), var(Is) -> % ???
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
        ( pstat_stat(PS, S) ->
            true
        ;
        writeln('Error: ill-formed pre/post condition'(PS))
        ),
        add_typed_anns(S, S1, VTm0, _VTm, [], _PolyVs),
        retractall(checking_pre_post),
        alias_stat(S1, VTm0, SS0, SS)
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
builtin_fdec((!io :: ref(ref('_bot')))). % '_bot' stops prying eyes
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
% builtin_tdef('_type_param'(_T), [dcons('_type_param', [void])]).
% we fudge things to get different data constructors for different type
% parameters (which are numbered), avoiding the potential for bogus
% sharing between terms of non-identical types.
% Current code for dc_type calls builtin_tdef with a var as the
% first arg, so there is an extra hack to avoid name being called with
% both arguments variables.  We could use a separate (faster) lookup for
% dc_type that avoids this.  It doesn't have have to work for these
% fudged data constructors - just the ones that can appear in source
% code (its used in processing case statements). Case statement
% processing seems like it might be the problem area for bogus sharing
% also, so if that is fixed we may be able to go back to the commented
% out version above.
builtin_tdef(TPN, [dcons(DC, [void])]) :-
    nonvar(TPN),
    TPN = '_type_param'(N),
    name(N, NCs),
    append(`_type_param_`, NCs, DCCs),
    name(DC, DCCs).
% XXX maybe void should be called unit but we are inflenced by C.
% Type void it has one value (void) so it requires
% zero bits to represent it. Its a bit special in the translation to C
% - C void functions don't really return any value and void in C
% doesn't have any values (this can break HO things potentially)
builtin_tdef(void, [dcons(void, [])]).
% We have a separate type called bottom ('_bot') that has no values. Due
% to strictness, any data constructor applied to bottom is bottom. We
% handle this specially when computing type paths; it is important
% because a function that returns values of a polymorphic type such as
% list(T) is restricted in what it can return (nil is the only value of
% this type). We use list('_bot') to generate type paths etc in this
% case.
builtin_tdef('_bot', []).
builtin_tdef(int, [dcons(xyzzy, [])]). % XXX
builtin_tdef(bool, [dcons(false, []), dcons(true, [])]).
builtin_tdef(ref(T), [dcons('_ref', [T])]).
builtin_tdef(list(T), [dcons(nil, []), dcons(cons, [T, list(T)])]).
builtin_tdef(maybe(T), [dcons(nothing, []), dcons(just, [T])]).
builtin_tdef(either(T1,T2), [dcons(left, [T1]), dcons(right, [T2])]).
builtin_tdef(pair(T1,T2), [dcons(t2, [T1, T2])]). % XX tuple naming?
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
% data_cons(pair(_,_)). % pair is type name, t2 is now constructor
data_cons('_type_param'(_)). % not needed?
data_cons('_cl0'(_,_)).
data_cons('_cl1'(_,_,_)).
data_cons('_cl2'(_,_,_,_)).
data_cons('_cl3'(_,_,_,_,_)).
data_cons('_cl4'(_,_,_,_,_,_)). % XXX add more
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
% and also from the precondition (where it may occur) but thats rather
% tricky.  It turns out that the extra params do no harm and are
% basically ignored later.  In the low level repersentation, types of
% closure arguments are given explicitly so there is no ambiguity (if
% the src code had t1 -> (...) sharing f(x1,x2)=x3 it would look like x1
% is a closure argument.
%
% We also handle implicit parameters. These are attached one level further in
% than is convenient:
% t1 -> t2 -> t3 implicit rw io sharing f(a)=r pre nosharing post nosharing
% is parsed as ->(t1,->(t2,sharing(implicit(t3,rw(io)...
% The "implicit" is found and processed at the same recursion level as t3 and
% the resulting type plus implicit params is returned from ctn1 wrapped up
% in implicit/4 then unwrapped at the higher level.  Implicit arguments 
% are inherited to outer arrows by default, thus the t1 -> ... type has
% rw(io) added to it's representation.  This can be overridden by nested uses
% of implicit, eg:
% t1 -> (t2 -> t3 implicit rw io) implicit ro foo
% has io for the inner arrow and foo for the outer arrow.  If we want to have
% implicit arguments for an inner arrow but nothing for an outer arrow we can
% use "implicit void".
canon_type_name(ST, T) :-
    ( ctn1([], ST, T1) ->
        T = T1
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
        L =.. [_Fn|LAs],
        get_bang_args(LAs, BVs, LAs1),
        ctn1([], STL, TL),
        append(Ts, [TL], Ts1),
        ctn1(Ts1, STR, TR),
%         ( nonvar(TR), TR = implicit(TR1, ROIs, RWIs, WOIs) ->
%             % next type down had implicit args declared
%             true
%         ;
%             % no implicit args declared (here at least)
%             TR1 = TR,
%             ROIs = [],
%             RWIs = [],
%             WOIs = []
%         ),
%         T = arrow(TL, TR1, BVs, LAs1, R, Pre, Post, Ts, ROIs, RWIs, WOIs)
        unwrap_implicit(TR, TR1, ROIs, RWIs, WOIs),
        T = arrow(TL, TR1, BVs, LAs1, R, Pre, Post, Ts, ROIs, RWIs, WOIs)
    ; ST = (STL -> STR), nonvar(STR), STR = (_ -> _) ->
        % arrow with RHS an arrow - need to recursively process RHS
        % and from the result infer the sharing for this arrow
        % Implicit args are inherited from RHS
        ctn1([], STL, TL),
        append(Ts, [TL], Ts1),
        ctn1(Ts1, STR, TR),
        TR = arrow(_, _, _RBVs, RLAs, RR, RPre, _, _, ROIs, RWIs, WOIs),
        % We say no vars are banged since we just create a closure
        % XXX is this the best choice? A function can smash some arguments
        % then return a closure.  Clarify how this can be declared and make
        % sure everything is safe with this treatment.
        length(Ts, NTs),
        NCLAs is NTs + 1,
        take(NCLAs, RLAs, CLAs),
        CL =.. [closure|CLAs],
        % T = arrow(TL, TR, [], CLAs, RR, RPre, RR = CL, Ts, _ROIs,
        % _RWIs, _WOIs)
        % previously inherited ROIs, RWIs from arrow to right - no longer
        % T = arrow(TL, TR, [], RLAs, RR, RPre, RR = CL, Ts, ROIs, RWIs, [])
        T = arrow(TL, TR, [], RLAs, RR, RPre, RR = CL, Ts, ROIs, RWIs, WOIs)
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
%         ( nonvar(TR),
%             TR = implicit(TR1, ROIs, RWIs, WOIs),
%             \+ (ROIs = [], RWIs = [], WOIs = [])
%         ->
%             % type further down had implicit args declared - use+inherit them
%             TI = arrow(TL, TR1, [], LAs, r, Pre, Post, Ts, ROIs, RWIs, WOIs),
%             T = implicit(TI, ROIs, RWIs, WOIs)
%         ;
%             % no implicit args declared for next arrow
%             TR1 = TR,
%             ROIs = [],
%             RWIs = [],
%             WOIs = [],
%             T = arrow(TL, TR1, [], LAs, r, Pre, Post, Ts, ROIs, RWIs, WOIs)
%         )
        unwrap_implicit(TR, TR1, ROIs, RWIs, WOIs),
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

% extract return type and implicit params from whatever ctn1 returns
unwrap_implicit(TR0, TR, ROIs, RWIs, WOIs) :-
        ( var(TR0) ->
            % type var (= Prolog var)
            TR = TR0,
            ROIs = [],
            RWIs = [],
            WOIs = []
        ; TR0 = implicit(TR, ROIs, RWIs, WOIs) ->
            % implicit args declared (one level down in Prolog term)
            true
        ; TR0 = arrow(_, _, _, _, _, _, _, _, ROIs, RWIs, WOIs) ->
            % implicit args possibly declared >1 level down and implicitly
            % inherited
            TR = TR0
        ; % non-arrow type and no implicit args declared
            TR = TR0,
            ROIs = [],
            RWIs = [],
            WOIs = []
        ).

% scan through comma-separated sequence of implicit parameters
% declared and return sorted lists of ro, rw, wo implicit params
% Note rw params are annotated with DU specs; others are not
% XXXX should check for repeated rw var with different DU specs
gather_implicits(Ic, ROIs, RWIs, WOIs) :-
    ( gather_imps(Ic, ROIs0, RWIs0, WOIs0) ->
        sort(ROIs0, ROIs),
        sort(RWIs0, RWIs),
        sort(WOIs0, WOIs),
        % check ROIs0, RWIs0, WOIs0 don't intersect
        ( member(V, ROIs), member(V^_, RWIs) ->
            writeln('Error: implicit parameter declared ro and rw:'(V))
        ; member(V, ROIs), member(V, WOIs) ->
            writeln('Error: implicit parameter declared ro and wo:'(V))
        ; member(V^_, RWIs), member(V, WOIs) ->
            writeln('Error: implicit parameter declared wo and rw:'(V))
        ;
            true
        )
    ;
        writeln('Error in implicit parameter declarations:'(Ic)),
        ROIs = [],
        RWIs = [],
        WOIs = []
    ).

% as above, returning unsorted lists
gather_imps(void, [], [], []). % explicit declaration of no implicit args
gather_imps((ro P), [P], [], []) :-
    ( state_var(P, _DUS) ->
        true
    ;
        writeln('Error: undefined state variable: '(P)),
        atom(P),
        DUS = (...!),
        assert(state_var(P, DUS))
    ).
gather_imps((rw P), [], [P^DUS], []) :-
    ( state_var(P, DUS) ->
        true
    ;
        writeln('Error: undefined state variable: '(P)),
        atom(P),
        DUS = (...!),
        assert(state_var(P, DUS))
    ).
% currently disallow duspec on rw state vars
% gather_imps((rw P), [], [P], []) :-
%     P = P1^_DUS,
%     atom(P1).
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
% allow/ignore type annotations XXX delete - what were they used for??
get_bang_args([], [], []).
get_bang_args([LA|LAs0], BVs, LAs) :-
    ( (LA = (!V) ; LA = (!V::_)), V = V1^_DUS, atom(V1) ->
        % Should check DUS is valid.  Have we processed type definitions
        % here? We need them to check validity.
        % XXXX valid_du_spec(DUS),
        BVs = [V|BVs1],
        LAs = [V1|LAs1]
    ; (LA = (!V) ; LA = (!V::_)), atom(V) ->
        BVs = [V^(...!)|BVs1], % default DU spec is all DU = ...(!)
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
    FH =.. [FName|_],
    writeln('    processing types etc. of '(FName)),
    % pstat_stat(CFB, FB), writeln(CFB), nl, writeq(FB), nl.
    ( pstat_stat(CFB, FB) ->
        true
    ;
        % XXX handle such errors better
        writeln('ERROR: dodgey definition:'(CFH = CFB)),
        pstat_stat(void, FB) % -> spurious errors but better than loop
    ).

% change function body so it assigns result to a var rather than
% implicit or explicit return, for inferred postconditions
% (XXX may not cover all cases, possibly should have done this
% processing after conversion to internal syntax, but here we are...)
% If we have a sequence of statements we leave them all untouched except
% the last. Based on pstat_stat code
pstat_fix_return(PS0, TRes, PS) :-
    ( var(PS0) ->
        % XX something major is wrong 
        writeln('ERROR: Prolog var encountered'),
        PS = (TRes = foobar)
    ; PS0 = (if C then A else B) ->
        pstat_fix_return((cases C of {case true: A case false: B}), TRes, PS)
    ; PS0 = (if C then A) ->
        pstat_fix_return((if C then A else void), TRes, PS)
    ; PS0 = {PS1} ->
        pstat_fix_return(PS1, TRes, PS)
    ; PS0 = (PS1 ; PS2) ->
        pstat_fix_return(PS2, TRes, PS3),
        PS = (PS1 ; PS3)
    % XXX explicit type info can now be attached to RHS, eg
    % *tp = (mt :: bst(int)) (need to clean up this old stuff?)
    % Leave so return expression can be cast
    ; PS0 = (PS1 :: T) -> % XX rethink explicit type decs?
        PS = (TRes = (PS1 :: T))
    ; PS0 = (_PE1 := _PE2) ->
        % XXX maybe we should traverse the whole of PS0 looking for
        % things we don't want in inferred postconditions
        writeln('ERROR: impure code not allowed in inferred postconditions'),
        PS = (TRes = void)
    ; PS0 = (PE1 = PE2) ->
        PS = (PE1 = PE2; TRes = void)
    ; PS0 = (_PS1 ! _V) ->
        writeln('ERROR: impure code not allowed in inferred postconditions'),
        PS = (TRes = void)
    ; PS0 = (cases PE of PCd) ->
        pcases_fix_return(PCd, TRes, PCd1),
        PS = (cases PE of PCd1)
    ; PS0 = return(PE1) ->
        PS = (TRes = PE1)
    ; PS0 = return ->
        PS = (TRes = void)
    ; % var or procedure call (better be the former!)
        PS = (TRes = PS0)
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
    % XXX explicit type info can now be attached to RHS, eg
    % *tp = (mt :: bst(int)) (need to clean up this old stuff?)
    % With explicit types, add extra typed(bst(int)) annotation and in
    % type analysis check inferred type is an instance.  Could allow for
    % var = var only, or add extra eqns and only check for annotation
    % for such eqns to simplify code.  Process in add_typed_anns_veq?
    ; PS = (PS1 :: T) -> % XX rethink explicit type decs?
        canon_type_name(T, T1),
        ( atom(PS1), \+ data_cons(PS1) ->
            V = PS1,
            Ann = [src(PS), typed(T1), decl_only(V)]
        ; PS1 = (!V), state_var(V, DUS) ->
            Ann = [src(PS), typed(T1), decl_only(V), bang(d, V^DUS)]
        ; PS1 = (!V), atom(V), \+ data_cons(V) ->
            Ann = [src(PS), typed(T1), decl_only(V), bang(d, V^(...!))]
        ; PS1 = (!V), V = V1^DUS, atom(V1), \+ data_cons(V1) ->
            check_duspec_on_state_var(V1, DUS, PS),
            % XXXX valid_du_spec(DUS),
            Ann = [src(PS), typed(T1), decl_only(V1), bang(d, V)]
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
        ( state_var(V, DUS) ->
            S2 = C1-[src(PS), bang(i, V^DUS)|Anns1]
        ; atom(V) ->
            S2 = C1-[src(PS), bang(i, V^(...!))|Anns1]
        ; V = V1^DUS, atom(V1) ->
            check_duspec_on_state_var(V1, DUS, PS),
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
        ( PE1 = !V1, state_var(V1, DUS) ->
            combine_stats(ES2, deref_eq(V1, V2)-[src(PEl=PEr), bang(d, V1^DUS)], S)
        ; PE1 = !V1, atomic(V1), \+ data_cons(V1) ->
            combine_stats(ES2, deref_eq(V1, V2)-[src(PEl=PEr), bang(d, V1^(...!))], S)
        ; PE1 = !V1, V1 = V1v^DUS, atomic(V1v), \+ data_cons(V1v) ->
            check_duspec_on_state_var(V1v, DUS, PEl=PEr),
            % XXXX valid_du_spec(DUS),
            combine_stats(ES2, deref_eq(V1v, V2)-[src(PEl=PEr), bang(d, V1)], S)
        ; PE1 = V1, atomic(V1), \+ data_cons(V1) ->
            combine_stats(ES2, deref_eq(V1, V2)-[src(PEl=PEr)], S)
        ;
            writeln('Error: illegal statement'(PEl = PEr)),
            S = empty_stat-[src(PEl=PEr)]
        )
    ; 
        % if LHS is not * it should be a var
        % (XXX could also allow type annotations here)
        ( atom(PEl) ->
            Vl = PEl,
            Anns = [src(PEl=PEr)],
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
                    ESs, S1),
                propogate_anns(S1, S)
            ; PEr = (!PEr1) ->
                % more repeated code - getting bad!
                functor(PEr1, F, Arity),
                ( func_arity(F, DecArity) -> % call known fn
                    % f(h,t) -> v = f(hv,tv)
                    PEr1 =.. [F|PEs],
                    map2(to_var, PEs, Vs, ESs),
                    ( Arity = DecArity ->
                        foldr(combine_stats,
                            eq_sapp(Vl, F, Vs)-[app_bang(F)|Anns],
                            ESs, S1),
                        propogate_anns(S1, S)
                    ; Arity < DecArity ->
                        foldr(combine_stats,
                            eq_papp(Vl, F, Vs)-[app_bang(F)|Anns],
                            ESs, S1),
                        propogate_anns(S1, S)
                    ;
                        % XX trf to eq_sapp(new, ...); eq_sapp(Vl, new,...)
                        writeln('Hyper-saturated applications not yet supported'(F)),
                        fail
                    )
                ; Arity > 0 -> % call state var closure with arg
                    PEr1 =.. [F|PEs],
                    map2(to_var, PEs, Vs, ESs),
                    foldr(combine_stats,
                        eq_app(Vl, F, Vs)-[app_bang(F)|Anns],
                        ESs, S1),
                    propogate_anns(S1, S)
                ; Arity = 1 ->
                    % XXX could count this as an error?
                    % XXX or support ^ + state vars
                    writeln('Warning: ignoring unexpected ! prefix:'(PEr)),
                    S = eq_var(Vl, PEr1)-Anns
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
                        ESs, S1),
                    propogate_anns(S1, S)
                ; Arity < DecArity ->
                    foldr(combine_stats,
                        eq_papp(Vl, F, Vs)-Anns,
                        ESs, S1),
                    propogate_anns(S1, S)
                ;
                    % XX trf to eq_sapp(new, ...); eq_sapp(Vl, new,...)
                    writeln('Hyper-saturated applications not yet supported'(F)),
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
                    eq_app(Vl, F, Vs)-Anns, ESs, S1),
                propogate_anns(S1, S)
            )
        ;
            write('ERROR: illegal LHS:'(PEl = PEr)),
            nl,
            S = empty_stat-[]
        )
    ).

% convert expression to var plus extra stat(s)
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
            ESs, ES1),
        propogate_anns(ES1, ES)
    % need to put * before defined functions otherwise indirection gets
    % treated as a partial application to multiplication (if we want the
    % latter we have to have another multiply fn)
    ; PE = (**PE1) ->
        to_var(*(*PE1), V, ES)
    ; PE = (***PE1) ->
        to_var(*(*(*PE1)), V, ES)
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
                ESs, ES1),
            propogate_anns(ES1, ES)
        ; Arity < DecArity ->
            foldr(combine_stats,
                eq_papp(V, F, Vs)-[],
                ESs, ES1),
            propogate_anns(ES1, ES)
        ;
            % XX trf to eq_sapp(new, ...); eq_sapp(PEl, % new,...)
            writeln('Hyper-saturated applications not yet supported'),
            fail
        )
    ; PE = abstract ->
        % always introduce an extra equation for abstract in case it is
        % the argument of a data constructor (other code assumes it is on
        % RHS of =)
        fresh_var(V),
        ES = eq_var(V, abstract)-[]
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
            ; state_var(PE1, DUS) ->
                V = PE1,
                ES = empty_stat-[bang(d, V^DUS)]
            ;
                V = PE1,
                ES = empty_stat-[bang(d, V^(...!))]
            )
        ; PE1 = PE1v^DUS, atom(PE1v) ->
                % XXX should pass in src statement for error messages
                check_duspec_on_state_var(PE1v, DUS, PE1v^DUS),
                V = PE1v,
                ES = empty_stat-[bang(d, PE1)]
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
            eq_app(V, F, Vs)-[], ESs, ES1),
        propogate_anns(ES1, ES)
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
        ES = empty_stat-[bang(d, V^ref(!))]
    ; PE = (!PE1) ->
        % XXX add support for explicit ^DUS?
        ( atom(PE1) ->
            write('Error: need * on LHS of := (added):'(PE)),
            nl,
            V = PE1,
            ES = empty_stat-[bang(d, V^ref(!))]
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

% like pstat_fix_return for case branches
% based on pcases_cases (var names confusing)
pcases_fix_return({CPCd}, TRes, Cs) :-
    pcases_fix_return(CPCd, TRes, Cs).
pcases_fix_return((case PCd), TRes, (case Cs)) :-
    pcases_fix_return1(PCd, TRes, Cs).

pcases_fix_return1(PCd, TRes, Cs) :-
    (PCd = ((PE:PS0) case PCd1) ->
        pstat_fix_return(PS0, TRes, PS),
        Cs = ((PE:PS) case Cs1),
        pcases_fix_return1(PCd1, TRes, Cs1)
    ; PCd = (PE:PS0) ->
        pstat_fix_return(PS0, TRes, PS),
        Cs = (PE:PS)
    ;
        pcases_fix_return(PCd, TRes, Cs)
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
% on all the stats we put them on, last_use isn't actually used -
% used_later is sufficient)
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
    findall(IBV, member(bang(i, IBV^_), Ann0), NIBVs),
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
    add_typed_anns(S, S1, VTm0, VTm, [], _PolyVs),
    writeln(S1),
    assoc_to_list(VTm, VTs),
    writeln(VTs).

% take stat with annotations and var-type+defined map, return same stat with
% extra typed annotations + new VT map. We need to keep types of all
% vars (for later sharing analysis) so we give an error message if a var
% is defined with different types, even in different case branches, and
% add a defined flag to the map to say if its defined in all possible
% paths to the current program point (eg, if its defined in all possible
% case branches, not just some).
% 
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
add_typed_anns(C0-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C0 = seq(Sa0, Sb0),
    add_typed_anns(Sa0, Sa, VTm0, VTm1, PolyVs0, PolyVs1),
    add_typed_anns(Sb0, Sb, VTm1, VTm, PolyVs1, PolyVs),
    C = seq(Sa, Sb),
    Ann = Ann0.
add_typed_anns(C0-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C0 = cases(V, Cases0),
    lookup_old_assoc(V, VTm0, TV, VTm1),
    % we want to keep track of types of all vars to use for type
    % folding in sharing analysis but also want vars defined in only
    % some branches of a case to be undefined in subsequent code. To do
    % this we have a flag with everything in the map to say its the var
    % is definitely defined (for all execution paths), keep all vars in
    % the map (definitely defined or not), and don't allow the same var
    % to be defined in different case branches with different types.
    % map_acc(add_typed_anns_case(TV), Cases0, Cases, VTm1, VTm,
    % PolyVs0, PolyVs),
    map_add_typed_anns_case(TV, Cases0, Cases, VTm1, VTms, PolyVs0, PolyVs),
    % XX would be more efficient if we just returned extra elements of
    % VTm
    vt_intersection(VTms, VTm),
    C = cases(V, Cases),
    Ann = [typed(TV)|Ann0].
add_typed_anns(eq_var(Vl, Vr)-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C = eq_var(Vl, VrA),
    TVl = Tl,
    TVr = Tr,
    add_typed_anns_veq(eq, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA, PolyVs0, PolyVs).
add_typed_anns(eq_deref(Vl, Vr)-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
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
    add_typed_anns_veq(eq, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA, PolyVs0, PolyVs).
add_typed_anns(deref_eq(Vl, Vr)-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C = deref_eq(Vl, VrA),
    TVl = ref(Tl),
    TVr = Tr,
    add_typed_anns_veq(eq, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA, PolyVs0, PolyVs).
add_typed_anns(assign(Vl, Vr)-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    % XX *!v := abstract a bit weird - disallow?
    C = assign(Vl, VrA), % same as deref_eq
    TVl = ref(Tl),
    TVr = Tr,
    add_typed_anns_veq(assign, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann, VrA, PolyVs0, PolyVs).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm, PolyVs, PolyVs) :-
    C = var_stat(V),
    % we once allowed var::type "statements" and treated them as declarations
    % before the var is defined
    % Now we allow var = (expr::type) instead
%     ( fail, member(typed(TV), Ann0) ->
%         ( get_assoc(V, VTm-_DF, _) ->
%             writeln('Error: redeclaration of type for '(V)),
%             write_src(Ann0)
%         ;
%             true
%         ),
%         put_assoc(V, VTm0, TV-def, VTm),
%         Ann = Ann0
%     ;
    lookup_assoc(V, VTm0, TV-def, VTm),
    % we add typed_rhs in case this is the last statement and
    % its converted to returnvar = V
    Ann = [typed(TV), typed_rhs(TV)|Ann0].
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm, PolyVs, PolyVs) :-
    C = empty_stat, % not needed?
    Ann = Ann0,
    VTm = VTm0.
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C = eq_dc(Vl, DC, Arity, Args),
    % similar to applications but we extract the types differently
    dc_type(DC, Arity, TDC, TDCArgs),
    add_typed_anns_dcapp(Vl, DC, TDC, Args, TDCArgs, TDC, Ann0, Ann, VTm0, VTm, PolyVs0, PolyVs).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C = eq_sapp(Vl, F, Args),
    nfdec_struct(F, TF),
    add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm0, VTm, PolyVs0, PolyVs).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C = eq_papp(Vl, F, Args),
    % same as eq_sapp
    nfdec_struct(F, TF),
    add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm0, VTm, PolyVs0, PolyVs).
add_typed_anns(C-Ann0, C-Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    C = eq_app(Vl, F, Args),
    % XX if type of Vl is not an arrow we can replace app by sapp
    % good for compilation but need to tweek sharing anal code(?)
    % same as eq_sapp except we lookup type of F in assoc
    lookup_old_assoc(F, VTm0, TF, VTm1),
    add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm1, VTm, PolyVs0, PolyVs).

% for function applications (arrow types)
% XX F passed in for error message - better to pass in src
add_typed_anns_app(Vl, F, TF, Args, Ann0, Ann, VTm0, VTm, PolyVs0, PolyVs) :-
    length(Args, Arity),
    extract_ret_type(Arity, TF, TFArgs, TFR),
    add_typed_anns_dcapp(Vl, F, TF, Args, TFArgs, TFR, Ann0, Ann, VTm0, VTm, PolyVs0, PolyVs).

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
% 
% XPOLY: New version of ensuring safety: Whenever we use a banged var
% (or a var that shares with one) with a polymorphic type, we
% instantiate the type of the var. If the var later gets used where a
% different instance of the type is expected there will be a type error.
% An advantage of this is that we don't need explicit casting of nil
% (for example) if a var is a pointer to an initially empty list that
% then gets updated. Its particularly beneficial for polymorphic code
% with destructive update of the non-polmorphic bits, eg the polymorphic
% version of cords where the nil needs to cast to a list of T, where T
% is the type parameter in the type signature (which currently we don't
% have access to in the function and use an ugly hack for now)
% 
% Unfortnately, type analysis is done before sharing/update analysis. We
% can rely on updated vars having ! in the source code so type analysis
% can be depend on it *except* that last uses of vars generally don't have
% to have !. To add to the inconvenience last_use and used_later are
% also added after type analysis.
% First attempt: any var with a polymorphic type at the end of type
% analysis is added to the used_later list, so last use isn't
% recognised. BUT a type vars can be instantiated to a (different,
% ground) type because a shared variable is updated - at the end of type
% checking the type is ground and there is no ! annotation on the last
% use of the var that used a different type.
% We need to do something special for the last occurrence of vars,
% since normally they may not be banged even though they are updated.
% We collect all vars with an initial polymorphic type and add all
% these to the used_later list, so last use isn't recognised and if
% these vars are updated 
% 
% XXXX BUG: for polymorphic higher order code we get bogus errors
% when the type of the call is not instantiated: postcondition has self
% sharing for type params whereas we expect just sharing for the
% instance. Why doesn't type/map get instantiated - thats intuitively
% what we want to do and could avoid this problem.
add_typed_anns_dcapp(Vl, F, TF, Args, TFArgs, TFR, Ann0, Ann, VTm0, VTm, PolyVs0, PolyVs) :-
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
        % copy_term(TCurrsc1, TCurrsc2),
        copy_term(TF-TFR-TFArgs, TFc1-TFRc1-TFArgsc1),
        unify_with_occurs_check(TCurrsc1, TFArgsc1)
    ->
        % check that !var type hasn't been instantiated
        % XPOLY XXXX need to handle arrows with deannotate_type
        map2(check_du_var_type_inst(Ann0), Args, TCurrsc1, TCurrs),
        % we put back the first annotation we see for each arrow type
        unify_first_arrows(TCurrsc, TFArgsc1),
        Tr = TFRc1
    ;
        VTm1 = VTm0,
        E =.. [F|Args],
        map_acc(flip_lookup_old_assoc, Args, TPCurrs, VTm0, _),
        writeln('ERROR: type error in arguments of application:'(E, TPCurrs, TFArgs)),
        write_src(Ann0),
        smash_type_vars(TFArgs), % proceed with some default type
        TFc1 = TF,
        Tr = TFR
    ),
    ( get_assoc(Vl, VTm1, TVl-_DF) -> 
        % we check if its a pre/postcondition using dynamic flag
        ( checking_pre_post ->
            % allow redefinition in pre+post conditions and (try to)
            % unify types on LHS and RHS
            ( unify_with_occurs_check(TVl, Tr) ->
                true
            ;
                writeln('ERROR: incompatible types in pre/post-condition'(TVl, Tr)),
                write_src(Ann0)
            )
        ;
            % could check DF and add "possibly" to error message
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
        put_assoc(Vl, VTm1, TVl-def, VTm2)
        % XXX Singleton variable in branch: TFc,Trc,TFArgsc ?????
        % Trc = Tr,
        % TFc = TF,
        % TFArgsc = TFArgs
    ),
    ( ground(TVl) ->
        PolyVs = PolyVs0
    ;
        PolyVs = [Vl|PolyVs0]
    ),
    % TFArgs has uninstantiated HO type, TCurrsc has instantiated HO
    % type (-> problem); TFArgsc1 has instantiated type (has been
    % unified but annotations not checked)
    % map(check_ho_types(Ann0, Vl-F-Args), TFArgs, TCurrsc), % XXX
    map(check_ho_types(Ann0, Vl-F-Args), TFArgsc1, TCurrsc),
    % we add annotations for both the fn app and dc cases - could merge?
    % typed_dc() no longer used...
    % Ann = [typed(TVl), typed_rhs(TFc), typed_dc(TCurrsc)|Ann0].
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
        % check definition of ro+rw vars; if there are no args we have a
        % closure and when the closure they are needed, but not here.
        % Do we need to count args and arrows to be
        % more general?  Usually implicit only occurs in the "last" arrow.
        % XXXX But maybe we are not catching all errors here because there may
        % be N args and N arrows with implicit in the rightmost (see also wo
        % args below)
        (   Args \= [],
            (member(I, ROIs) ; member(I^_, RWIs)),
            \+ get_assoc(I, VTm0, _),
            writeln('Error: undeclared implicit argument: '(F, I)),
            write_src(Ann0),
            fail
        ;
            true
        ),
        % check redefinition of wo vars (see ro+rw above)
        (   Args \= [],
            member(WOV, WOIs),
            get_assoc(WOV, VTm2, TWOV-_),
            writeln('Error: state variable redefined '(WOV :: TWOV)),
            write_src(Ann0)
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

% if var V has a bang annotation, the type may need further
% instantiation
% XPOLY now we just unify types TV1 is the instantiated copy for this
% call; TV2 is the earlier, possibly more general type from the type map
check_du_var_type_inst(Ann, V, TV1, TV2) :-
    ( member(bang(_, V), Ann), \+ variant(TV1, TV2) ->
        % XXX can get bogus looking warnings here because type annotations are
        % stripped from arrow types but types might be the same but with
        % renamed variables, eg T->T then T1->T1
        % We use the ground check below to reduce messages but still get
        % some.  The variant check should just ignore annotations.
        % XXX Do we check annotations are compatible?  Ideally we could
        % do a form of unification with annotations, possibly adding
        % preconditions from one arrow type and deleting postconditions
        % from the other (not sure allowing such code is wise!).
        ( ground(TV2) ->
            true
        ;
            writeln('Warning: instantiating type of updated variable'(V::TV2)),
            (TV1 = TV2 ->
                writeln('  new type'(TV1))
            ;
                writeln('Oops: can\'t unify types')
            ),
            write_src(Ann)
        )
    ;
        true
    ).

% equality for (possibly deref) vars
% For left and right sides we pass in var, type, and type of var.
% The latter two will be either identical vars or T and ref(T),
% depending on form of equality
add_typed_anns_veq(AEQ, Vl, Tl, TVl, Vr, Tr, TVr, VTm0, VTm, Ann0, Ann,
VrA, PolyVs0, PolyVs) :-
    % type of Vr should already be known (special case for abstract)
    % if its known and not ref(_) but TVr=ref(_) its an error
    ( Vr = abstract ->
        ( get_assoc(Vl, VTm0, TVl3-_) ->
            VTm1a = VTm0
        ;
            % from default processing of arrow type we sometimes get
            % extra v=abstract eqns where v is only an arg for inner
            % arrows; here we just set the type to void
            % XXXXA sometimes handy to add x=abstract in pre/post where x
            % is yet to be defined -> better to use type var if it causes
            % no problems (fingers crossed!)
            % put_assoc(Vl, VTm0, void-def, VTm1a)
            put_assoc(Vl, VTm0, Tlc-def, VTm1a) % Tlc filled in below
        ),
        % lookup_old_assoc(Vl, VTm0, TVl3, VTm1a),
        copy_term(foo(Tl, TVl, TVl3), foo(Tlc, TVlc, TVl3c)),
        TVl3c = TVlc, % instantiates Tlc
        % smash_type_vars(Tlc), % we actually want to retain type var
        VrA = abstract(Tlc),
        put_assoc(VrA, VTm1a, Tl-def, VTm1)
        % ignore PolyVs for abstract
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
    ( get_assoc(Vl, VTm1, TVl0-_) -> 
        % we check if its a pre/postcondition using dynamic flag
        ( AEQ = eq, \+ checking_pre_post ->
            % could check DF and add "possibly"
            writeln('Error: variable redefined '(Vl :: TVl0)),
            write_src(Ann0)
        ;
            % XXXX Oops! alias_stat failed! if pre/post has p=v instead of *p=v
            true
        ),
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
            check_ho_types(Ann0, Vl=Vr, Tl, Trc)
        ; AEQ = eq, checking_pre_post -> % allow redefinition etc
            Tl = Tr1
        ; AEQ = assign, subsumes_chk(Tl, Tr1) ->
            % XPOLY for assignment we allow Tl to be further
            % instantiated by Tr1
            writeln('Note: instantiating type of updated variable'(Vl::TVl)),
            Tl = Tr1,
            writeln('  new type'(TVl)),
            write_src(Ann0)
        ;
            writeln('Error: type error in var equality/assignment:'(((Vl::TVl), (Vr::TVr)))),
            write_src(Ann0)
        ),
        VTm = VTm1,
        PolyVs = PolyVs0,
        Casts = []
    ; member(typed(TVl0), Ann0) ->  % :: T annotation on RHS
        % xxx(member(typed(TVl0), Ann0)),
        % check TVl0 is lesseq general than Tr
        copy_term(Tr, Trc),
        ( Trc == Tr -> % worth bothering??
            Casts = []
        ;
            Casts = [Vr]
        ),
        deannotate_type(Trc, Tr1),
        % subsumes_chk is the name in older versions
        ( subsumes_chk(Tr1, TVl0) ->
            Tr1 = Tl,
            check_ho_types(Ann0, Vl=Vr, TVl0, Trc),
            % unify Tr with Trc that may share vars with Tr1 and Tl
            Tr = Trc
        ;
            writeln('Error: type error in var equality/assignment:'(((Vl::TVl), (Vr::TVr)))),
            write_src(Ann0)
        ),
        % assuming this unification succeeds, it can propagate type
        % cast (:: TVl0) backwards to where Vr was defined
        ( TVl = TVl0 -> % want instantiation here
            true
        ;
            writeln('Error: expected ref type for '(Vl, TVl0)),
            write_src(Ann0)
            % XX do something to help carry on here rather than fail?
        ),
        ( ground(TVl0) ->
            PolyVs = PolyVs0
        ;
            PolyVs = [Vl|PolyVs0]
        ),
        put_assoc(Vl, VTm1, TVl0-def, VTm)
    ;
        (AEQ = assign -> % := with no prior assignment - dodgey
            writeln('Warning: assigned variable not previously defined '(Vl)),
            write_src(Ann0)
        ;
            true
        ),
        Tl = Tr,
        ( ground(TVl) ->
            PolyVs = PolyVs0
        ;
            PolyVs = [Vl|PolyVs0]
        ),
        put_assoc(Vl, VTm1, TVl-def, VTm),
        Trc = Tr,
        Casts = []
    ),
    Ann = [typed(Tl), typed_rhs(Trc), casts(Casts)|Ann0].

% infer types for case branch
% first arg is current known type of case var
% XXX add case_def
add_typed_anns_case(TV, case_dc(DC, Arity, PArgs, S0),
                     case_dc(DC, Arity, PArgs, S), VTm0, VTm, PolyVs0, PolyVs) :-
    dc_type(DC, Arity, TDC, TDCArgs),
    map('X,ref(X)', TDCArgs, TRDCArgs),
    % PArgs is (deref) pattern vars
    % TRDCArgs is expected types of above from DC with implicit refs
    % XXX should use get_assoc etc so we can check for redefinition of vars
    % maybe have new_lookup_assoc and flip_new_lookup_assoc preds
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
    add_typed_anns(S0, S, VTm1, VTm, PolyVs0, PolyVs).

% take list of VTs from cases and get intersection
% YYY rename: now returns the union, but if you ignore elements with the
% def flag = undef then its the intersection, so effectively the
% resulting map represents both the union (which we need for sharing
% analyis later) and the intersection (which we need for var undefined
% messages).  Should rename some variables also - VT -> VTD?
% XX must be a more efficient way (should be in assoc library?)...
% Asymetry wrt cases so some warnings will be missed?
vt_intersection(VTms0, VTm) :-
    map(assoc_to_list, VTms0, VTss),
    append(VTss, VTs),
    sort(VTs, VTs1), % remove duplicates
    empty_assoc(VTme),
    map0_acc(add_assoc_if_in_all(VTms0), VTs1, VTme, VTm).

% check V-T is def in each of VTms0 and if so, add it to VTm0 with def flag,
% otherwise add if with DF=undef
add_assoc_if_in_all(VTms0, V - (T-DF), VTm0, VTm) :-
    ( DF = def, map0(check_get_assoc(V, T), VTms0) ->
        put_assoc(V, VTm0, T-def, VTm)
    ;
        put_assoc(V, VTm0, T-undef, VTm)
    ).

% check V has type T in VTs (if it has another type, issue error) and is
% definitely defined.  If types are not identical but can be unifed we
% allow it and issue a warning (hopefully occurs check not required! XXX)
check_get_assoc(V, T, VTm) :-
    (get_assoc(V, VTm, T1-DF) ->
        (T1 == T ->
            true
        ; T1 = T ->
            % Allow polmorphic types to be instantiated without cast, eg
            % v = nil in one branch and v = cons(42,nil) in another
            writeln('Warning: instantiating type '(V :: T))
        ;
            writeln('Error: same var name with different types: '(V)),
            fail
        ),
        DF = def
    ;
        fail
    ).

% As above for list of cases - return list of case branches + VTms
map_add_typed_anns_case(_, [], [], _, [], PolyVs, PolyVs).
map_add_typed_anns_case(TV, [Case0|Cases0], [Case|Cases], VTm0, [VTm|VTms], PolyVs0, PolyVs) :-
    add_typed_anns_case(TV, Case0, Case, VTm0, VTm, PolyVs0, PolyVs1),
    map_add_typed_anns_case(TV, Cases0, Cases, VTm0, VTms, PolyVs1, PolyVs).

% like copy_term but we first strip sharing/mutability info from arrow
% types
copy_type_term(T0, T) :-
    deannotate_type(T0, T1),
    copy_term(T1, T).

% strip sharing/mutability info from arrow types
% doesn't strip implicit arguments
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

% lookup_assoc with last two args flipped, adds def flag
flip_lookup_assoc(V, TV, VTm0, VTm) :-
    lookup_assoc(V, VTm0, TV-def, VTm).

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
%     sum_ref(type_name, sum) ; % like sum(type_name, [prod('_ref', 1, [sum])]) above
%     sum_ref_anc(type_name, int). % like sum(type_name, [prod('_ref', 1, sum_anc(int))]) above
%     - added type_name for new type path code
% 
% Note also that at the top level we can't have sum_ref_anc(i) (i>=2 generally
% so these nodes must be lower in the tree).  This isn't encoded in the
% type.  Also not encoded is the constraint that the list of children of
% prod nodes must all be defined by either sum_ref or sum_ref_anc
% (the arguments of "normal" data constructors must be refs).  We
% also allow refs to refs to refs etc (the child of sum_ref can be
% sum_ref or sum_ref_anc), which doesn't correspond so
% directly to a traditional ADT.
% 
% Example from wam.pns (contains mutual recursion):
% type fs ---> f0 ; f1 ; f2.
% type term ---> var(term) ; nv(fs, terms).
% type terms ---> nil ; cons(term, terms).
% Gives the following representation:
% type_struct(fs,
%     sum(fs, [prod(f0, 0, []), prod(f1, 0, []), prod(f2, 0, [])])).
% type_struct(term, sum(term,
%     [prod(var, 1, [sum_ref_anc(2)]),
%      prod(nv, 2, [sum_ref(ref(fs), sum(fs,
%         [prod(f0, 0, []), prod(f1, 0, []), prod(f2, 0, [])])),
%         sum_ref(ref(terms), sum(terms,
%             [prod(nil, 0, []), prod(cons, 2, [sum_ref_anc(4), sum_ref_anc(2)])]))])])).
% type_struct(terms, sum(terms,
%     [prod(nil, 0, []),
%      prod(cons, 2, [sum_ref(ref(term), sum(term,
%         [prod(var, 1, [sum_ref_anc(2)]),
%          prod(nv, 2, [sum_ref(ref(fs), sum(fs,
%             [prod(f0, 0, []), prod(f1, 0, []), prod(f2, 0, [])])),
%             sum_ref_anc(4)])])),
%         sum_ref_anc(2)])])).
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
%
% This can be called with non-ground types, such as list(list(_)), which
% previously caused problems; we now replace type vars with ref(void) in
% the struct created (XXX should test with tricky polymorphic code more)
type_struct(T0, S) :-
    ( ground(T0) ->
        T = T0
    ;
        replace_vars(ref(void), T0, T)
    ),
    ( T = arrow(_, _, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) ->
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

% copy T0 to T, replacing any vars with R
replace_vars(R, T0, T) :-
    ( var(T0) ->
        T = R
    ;
        T0 =.. [F|Args0],
        map(replace_vars(R), Args0, Args),
        T =.. [F|Args]
    ).

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
        % type_ref_sum(TDefs, [TName|Ancs], TName1, Sum)
        type_ref_sum(TDefs, Ancs, TName1, Sum)
    ;
        Sum = sum(TName, Prods),
        map(cons_types_prod(TDefs, [TName|Ancs]), CTs, Prods)
    ).

cons_types_prod(TDefs, Ancs, dcons(DC, Ts), prod(DC, Arity, Sums)) :-
    length(Ts, Arity),
    map(type_ref_sum(TDefs, Ancs), Ts, Sums).

type_ref_sum(TDefs, Ancs, TName, Sum) :-
    ( nth1(N, Ancs, ref(TName)) -> % *first* check for ref(TName) ancestor
        Sum = sum_anc(ref(TName), N)
    ; nth1(N, Ancs, TName) -> % then check for TName ancestor
        N1 is N + 1,
        Sum = sum_ref_anc(ref(TName), N1)
    ;
        Sum = sum_ref(ref(TName), Sum1),
        % member(tdef(TName, CTs), TDefs),
        ( TName = arrow(_, _, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs) ->
            Sum1 = TName
        ;
            tdef(TName, CTs),
            type_sum(TDefs, [ref(TName)|Ancs], TName, CTs, Sum1)
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

% var was introduced by fresh_var
once_fresh_var(V) :-
    name(V, [0'V|_]).

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
% Type also passed in for path folding (probably should pass lvar and
% its path as separate args)
% XXXXX problem: top level type for aliased vars is unknown and could be
% different for different members of AVPs, eg, we could have a
% list(bool) var and a maybe(list(bool)) var both aliased to LHS. For
% type folding we currently need the top level type....
add_sharing_for_lhs_aliases(_T, _VTm, _LVP, [], _AVPs, SS, SS).
add_sharing_for_lhs_aliases(T, VTm, LVP, [ELVP|ELVPs], AVPs, SS0, SS) :-
    app_var_path(LVP, RestVPC, ELVP),
    add_sharing_for_lhs_aliases1(T, VTm, ELVP, RestVPC, AVPs, SS0, SS1),
    add_sharing_for_lhs_aliases(T, VTm, LVP, ELVPs, AVPs, SS1, SS).

% as above for single "extension" of LVP path
add_sharing_for_lhs_aliases1(_T, _VTm, _ELVP, _VPC, [], SS, SS).
add_sharing_for_lhs_aliases1(T, VTm, ELVP, VPC, [AVP|AVPs], SS0, SS) :-
    app_var_path(AVP, VPC, vp(V, EAP)),
    % XXX may need to fold path...
    % Need special case for V=abstract(_) since its not in VTm
    ( V = abstract(VT0) ->
    
        VT = VT0
    ;
        get_assoc(V, VTm, VT-_)
    ),
    fold_type_path(VT, EAP, EAPF),
    EAVPF = vp(V, EAPF),
    mk_alias_pair(ELVP, EAVPF, S),
    mk_alias_pair(ELVP, ELVP, S1),
    mk_alias_pair(EAVPF, EAVPF, S2),
    add_sharing_for_lhs_aliases1(T, VTm, ELVP, VPC, AVPs, [S1,S2,S|SS0], SS).

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
    (   member(V1^_, [abstract(_)^_|DUs])
    ;   member(V2^_, [abstract(_)^_|DUs])
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
% more precise.  Eg, *lp := cons(a, *lp) can modify *lp but it can't modify
% things which share with the elements of *lp.  In general, things lower
% in type tree are safe from modification - could check length of var
% paths etc.  We now specialise for LHS of assignment statements
% (see _lhs preds below) and can use more precise duspecs at least.
% XXX currently pass in annotations to see what vars are used later
% - should really just be removing all these from sharing set (need to
% keep track of what vars we need to keep for pre/postconditions
% though).
% Elsewhere we check all calls with implicit args are banged - we use
% app_bang annotations rather than bang for these
check_banged(BVs, MVs, SS, Ann, Stat, VTm) :-
    ( setof(MV, should_bang(MVs, SS, MV, VTm), Vs1) -> % Note setof can fail
        check_banged1(BVs, Vs1, SS, Ann, Stat, VTm)
    ;
        true
    ).

% as above, specialised for single modified var on LHS of assignment
% XX probably should bang LV even if its not used (or give warning)
check_banged_lhs(LV, BVs, SS, Ann, Stat, VTm) :-
    (   setof(MVP, should_bang_lhs(LV, SS, MVP), VPs1) -> % Note setof can fail
        check_banged_lhs1(BVs, VPs1, SS, Ann, Stat, VTm)
    ;
        true
    ).

% as above with all possibly modified vars
% BVs is vars with duspecs attached, AMVs is all modified var paths
check_banged1(BVs, AMVs, SS, Ann, Stat, VTm) :-
    % iterate over all members of AMVs
    (   member(VP, AMVs),
        VP = vp(V, VPC),
        % skip error messages about generated var names
        % - check atomic in case its abstract(_)
        \+ (atomic(V), once_fresh_var(V)),
        % ignore dead vars (use -> in case used_later() is missing)
        % note we allow update of dead vars which share with abstract -
        % this allows greater flexibility in coding and there are
        % reasonable uses of it.  note abstract() gets ignored here
        % XXX really? seems a bit suspect??
        ( member(used_later(ULVs), Ann) ->
            member(V, ULVs)
        ;
            true
        ),
        get_assoc(V, VTm, VType-_), % get type for checking duspec
        % \+ (member(last_use(LUVs), Ann), member(V, LUVs)),
        % we check for du of abstract vars, even if they are banged
        % note we need to check for sharing with abstract, not
        % V=abstract(_)
        (   aliases(SS, vp(V, VVP), vp(abstract(_AT), _AVP)),
            VVP \= vpe, % ??? We avoid empty paths now anyway
            member(V^VDUS, BVs),
            % if VVP might be updated we might be updating something that
            % shares with abstract
            du_spec_vpc_poss_bang(VDUS, VType, VVP)
        ->
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
        % ignore banged vars with duspecs that (definitely) allow
        % DU for this path
        \+ ( member(V^VDUS, BVs), du_spec_vpc_def_bang(VDUS, VType, VPC)),
        % must be an error...
        write('Error: variable path '),
        print(VP),
        write(' might be modified by '),
        print(Stat),
        nl,
        write_src(Ann),
        fail
    ;
        true
    ).

% like check_banged1 but we pass in modified variable paths, not variables
check_banged_lhs1(BVs, AMVPs, SS, Ann, _Stat, VTm) :-
    % print(check_banged_lhs1(BVs, AMVPs, SS, Ann, Stat)), nl,
    % iterate over all members of AMVs
    (   member(VP, AMVPs),
        VP = vp(V, VPC),
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
        % XXX really? seems a bit suspect??
        ( member(used_later(ULVs), Ann) ->
            member(V, ULVs)
        ;
            true
        ),
        % we check for du of abstract vars, even if they are banged
        % note we need to check for sharing with abstract, not
        % V=abstract(_)
        ( aliases(SS, VP, vp(abstract(_AT), _AVP)) ->
            write('Error: abstract variable path '),
            print(V),
            print(VPC),
            write(' might be modified'),
            % print(Stat),
            nl,
            write_src(Ann),
            fail
        ;
            true
        ),
        get_assoc(V, VTm, VType-_), % get type for checking duspec
        % ignore banged vars with path definitely covered by duspec
        \+ (member(V^DUS, BVs), du_spec_vpc_def_bang(DUS, VType, VPC)),
        % must be an error...
        write('Error: variable path '),
        write(V),
        print(VPC),
        write(' might be modified'),
        % print(Stat),
        nl,
        write_src(Ann),
        fail
    ;
        true
    ).

% Given list of varpaths which may be modified, and sharing set,
% (nondeterministically) return var path which may be modified
should_bang(MVs, SS, MVP, VTm) :-
    member(V1^DUS, MVs),
    MVP1 = vp(V1, VP1),
    member(s(MVP1, MVP1), SS),          % look for self-sharing
    get_assoc(V1, VTm, V1Type-_), % get type for checking duspec
    du_spec_vpc_poss_bang(DUS, V1Type, VP1),
    (   MVP = MVP1
    ;
        member(s(MVP1, MVP), SS)
    ;
        member(s(MVP, MVP1), SS)
    ).

% as above, specialised for single modified var on LHS of assignment
should_bang_lhs(LMVP, SS, MVP) :-
    (
        member(s(LMVP, MVP), SS)
    ;
        member(s(MVP, LMVP), SS)
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
    % app_var_path(_, vpc(C1, A1, N1, vpc('_ref', 1, 1, vpe)), VP1),
    % app_var_path(_, vpc(C2, A2, N2, vpc('_ref', 1, 1, vpe)), VP2),
    app_var_path(_, vpc(C1, A1, N1,  vpe), VP1),
    app_var_path(_, vpc(C2, A2, N2,  vpe), VP2),
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
% XXX NOTE: clause order matters!  We have two versions (see below)
% fold_type_path splits a var paths in two and it commits to the
% first solution satisfying certain conditions.
app_vpc(vpe, VPC, VPC).
app_vpc(vpc(C, A, N, VPC1), VPC2, vpc(C, A, N, VPC)) :-
    app_vpc(VPC1, VPC2, VPC).

% As above with clause/solution order reversed
app_vpc_order_rev(vpc(C, A, N, VPC1), VPC2, vpc(C, A, N, VPC)) :-
    app_vpc_order_rev(VPC1, VPC2, VPC).
app_vpc_order_rev(vpe, VPC, VPC).


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
%     sort(Ps1, Ps). % remove any dups from multiple sum_ref_anc()
% 
% % as above for sum type, given path so far to prefix
% type_paths_sum(P0, sum(_, Prod), Ps) :-
%     map0_acc(type_paths_prod(P0), Prod, [], Ps).
% type_paths_sum(P0, ref(_, Sum), [P|Ps]) :-
%     app_vpc(P0, vpc(ref, 1, 1, vpe), P),
%     type_paths_prod(P0, prod(ref, 1, [Sum]), [], Ps).
% type_paths_sum(P0, sum_ref_anc(N), [P]) :-
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
% We generate all var paths+info for the type then look for pairs of
% paths that have compatible info - same type plus DC,Argnum the same or
% one is _ref
type_var_self_share(T, V, Ss) :-
    type_paths_info(T, PIs),
    ( PIs = [] ->
        Ss = []
    ;
        setof(P1-P2, path_info_compat_pairs(PIs, P1, P2), PPs),
        map(ppair_alias(V), PPs, Ss)
    ).

% from list of var paths plus info, return compatible pairs
path_info_compat_pairs(PIs, P1, P2) :-
    % use append to split list so we don't return everything twice
    append(_, [P1-pinfo(DC1, A1, T)|PIs1], PIs),
    (   P2 = P1 % return self-share paths
    ;
        member(P2-pinfo(DC2, A2, T), PIs1), % type of later path is the same
        (   DC2 = DC1, A2 = A1          % same DC,Argnum
        ;
            DC1 = '_ref', DC2 \= '_ref' % one DC is _ref
        ;
            DC2 = '_ref', DC1 \= '_ref' % one DC is _ref
        )
    ).

% given var and pair of paths, return self_share
ppair_alias(V, P1-P2, S) :-
    mk_alias_pair(vp(V, P1), vp(V, P2), S).

% return all var paths which may share corresponding to a type
type_var_paths(T, V, VPs) :-
    type_paths(T, Ps),
    map(mk_vp(V), Ps, VPs).

mk_vp(X,P,vp(X,P)).

% return all paths which may share corresponding to a (canonical) type
% YY might be worth caching this
% New version without extra (implicit) refs in path and without empty paths.
% We recurse down different branches of the type, returning each path to
% a ref/1, but stop when there is an ancestor with the same type.
% Although type_struct can have sum_anc nodes referring back to the root
% of the tree, empty paths are avoided. This makes the sharing domain a
% little larger but makes sharing more precise.  Importantly, it allows
% the programming pattern *xp = x1; *!xp := x2; *!xp := x3 without bogus
% sharing of x1, x2 an x3, even if they have recurive types such as
% list(t) (previous version had sharing due to the empty path being used
% for such types). This assumes there is no recursion through a ref. For
% types such as ref(r1rr) below, there is still bogus sharing.  Maybe we
% could stop recursion when there is an ancestor with the same type and the
% same function symbol wrapper, so a list(int) in a top level ref would
% not be the same as the list(int) inside a cons.  This would still be a
% problem for types like ref(r1rr) with explicit refs. Doesn't seem to be
% easy to solve this imprecision.  XXX migt be good to implement the
% same fn symbol+type method at least?
% Examples:
% from rectype.pns:
% (note difference from sharing paper in rtree example)
% ?- type_paths(maybe(maybe(either(int, int))), Ps).
% Ps = [.just, .just.just, .just.just.left, .just.just.right].
% ?- type_paths(maybe(maybe(either(int, ref(int)))), Ps). % explicit ref
% Ps = [.just, .just.just, .just.just.left, .just.just.right, .just.just.right._ref].
% ?- type_paths(rtree, Ps). % recursion via list(rtree)
% Ps = [.rnode/2.1, .rnode/2.2, .rnode/2.2.cons/2.1, .rnode/2.2.cons/2.2].
% ?- type_paths(list(rtree), Ps).
% Ps = [.cons/2.1, .cons/2.1.rnode/2.1, .cons/2.1.rnode/2.2, .cons/2.2].
% ?- type_paths(r1r, Ps). % recursion via ref(r1r)
% Ps = [.r1rc, .r1rc._ref].
% ?- type_paths(r1rr, Ps). % recursion via ref(ref(r1rr))
% Ps = [.r1rrc, .r1rrc._ref, .r1rrc._ref._ref].
% ?- type_paths(ref(r1rr), Ps).
% Ps = [._ref, ._ref.r1rrc, ._ref.r1rrc._ref].
% ?- type_paths(ref(ref(r1rr)), Ps).
% Ps = [._ref, ._ref._ref, ._ref._ref.r1rrc].
type_paths(T, Ps) :-
    type_struct(T, TS),
    ( setof(P, PInfo^type_path_sum(TS, [], P, vpef, PInfo), Ps) ->
        true
    ;
        Ps = []
    ).

% As above but returns path info with each path
% YY might be worth caching this
type_paths_info(T, Ps) :-
    type_struct(T, TS),
    ( setof(P-PInfo, type_path_sum(TS, [], P, vpef, PInfo), Ps) ->
        true
    ;
        Ps = []
    ).

% % check if type is atomic (has only constants, so no sharing possible)
% atomic_type(T) :-
%     \+ (
%         type_struct(T, TS),
%         type_path_sum(TS, [], _P, vpef, PInfo)
%     ).

% nondeterministically return valid path given type and ancestors
% (ancestors include ref types for DC arguments - for proper
% folding when there are explicit refs in a recursive type)
% Also returns info about the location at the end of the path:
% the DC,ArgNum enclosing it (could be _ref,1) plus the type
% When we generate
% self-sharing for input args, add sharing for each pair of paths with
% same type and *compatible* DC+argnumber wrapper (ie, DC+argnumbers are
% the same or at least one is a ref
% The type in the info returned for arrow types is arrow/11 and the
% DC,Argnum is '_arrow',1. Closures are a bit tricky (XXX check):
% we pass in a flag, either vpef (to generate just empty paths where
% there might actually be closure arguments - we don't know what
% the types or data constructors are so these are just placeholders -
% should do more testing and thinking about this) or varf, where instead
% of vpe we add a fresh variables (this is so fold_type_path can
% match it with any existing path within a closure argument)
% XXX This is a nasty hack - might want to rethink it. Current code
% suffers from a history or attempts to reuse code for generating paths
% and folding/truncating them.
% XXXX Possible BUG if we have a function as an argument and it has two
% closure arguments that share - how is that captured with the current
% self-sharing code for input arguments? We need to look at self-sharing
% of actual arguments but not trigger precondition violation errors.
% Maybe its OK because arrow type should give info about possible
% sharing between closure arguments? But we should use this info in the
% arrow type to add sharing for closures in the formal arguments.
% Pawns fn could input a function with two closures that share, call the
% function and extract the two arguments in two separate variables,
% smash one, and the other will get smashed but the need for ! may be
% missed.
type_path_sum(Sum, Ancs, P, AF, PInfo) :-
    sum_to_type(Sum, T),
    % (writeln(T+Ancs) ; writeln(T-Ancs), fail),
    type_path_sum1(Sum, [T|Ancs], P, AF, PInfo).

type_path_sum1(sum(_, Prod), Ancs, P, AF, PInfo) :-
    type_path_prod(Prod, Ancs, P, AF, PInfo).
type_path_sum1(sum_ref(ref(T), Sum), Ancs, P, AF, PInfo) :-
    P = vpc('_ref', 1, 1, P1),
    (   P1 = vpe,
        PInfo = pinfo('_ref', 1, T)
    ;
        type_path_sum(Sum, Ancs, P1, AF, PInfo)
    ).
% type_path_sum1(sum_anc(_, _), _Ancs, vpef, AF, PInfo). % never get this?
type_path_sum1(sum_ref_anc(ref(T), _), _Ancs,
            vpc('_ref', 1, 1, vpe), _AF, pinfo('_ref', 1, T)).
type_path_sum1(Arrow, _Ancs, P, AF, PInfo) :-
    Arrow = arrow(_, TypeR, _, _, _, _, _, _, _ROIs, _RWIs, _WOIs),
    (AF = vpef ->
        VPR = vpe
    ;
        VPR = _ % return uninstantiated path for fold_type_path
    ),
    P = vpc(cla(CAN), 1, 1, VPR),
    % #closure args = #arrows in TypeR + 1
    arrow_num(TypeR, NCAR),
    NCA is NCAR + 1,
    between(1, NCA, CAN),
    % pinfo details not used but we want them distinct to avoid bogus sharing
    % pairs being introduced, eg ref(arrowtype) and ref(closure of
    % arrowtype)
    PInfo = pinfo('_arrow', 1, CAN-Arrow).

% as above but called with arg of a product (data constructor) so it
% must be a ref (made explicit in the ref view that type_struct
% currently returns but we don't really want it)
% XX check Ancs...?OK
type_path_ref(sum_ref(ref(T), Sum), Ancs, P, AF, DC, ANum, PInfo) :-
    (   P = vpe,
        PInfo = pinfo(DC, ANum, T)
    ;
        type_path_sum(Sum, Ancs, P, AF, PInfo)
    ).
type_path_ref(sum_ref_anc(ref(T), _), _, vpe,
            _AF, DC, ANum, pinfo(DC, ANum, T)).
type_path_ref(sum_anc(ref(T), _), _, vpe,
            _AF, DC, ANum, pinfo(DC, ANum, T)).

% as above for prod type (list of DCs)
% Note, we need a special case to deal with data constructors that
% have an argument of type _bot. There are no such computed values. We need
% to just skip this such data constructors.  Eg for list(_bot), we skip
% the cons/2 data constructor (and nil has no paths either; nil is the
% only value of this type 
type_path_prod(DCs, Ancs, P, AF, PInfo) :-
    member(prod(DC, Arity, Sums), DCs),
    \+ (has_bot_arg(Sums)),
    between(1, Arity, ANum),
    nth1(ANum, Sums, Sum),
    sum_to_type(Sum, ref(T)),
    % \+ member(ref(T), Ancs), % avoids >1 path with same type for refs
    P = vpc(DC, Arity, ANum, P1),
    type_path_ref(Sum, [ref(T)|Ancs], P1, AF, DC, ANum, PInfo).

% checks if _bot is in list of sum_ref types
has_bot_arg(Sums) :-
    member(sum_ref(ref('_bot'), _), Sums).

% change rep so we always have type name paired with sum
sum_to_type(sum(T, _), T).
sum_to_type(sum_ref(T, _), T).
sum_to_type(sum_anc(T, _), T).
sum_to_type(sum_ref_anc(T, _), T).
sum_to_type(arrow(_, _, _, _, _, _, _, _, _, _, _), void).

% for type T, P is a path which may be too long (extends beyond a
% sum_ref_anc() node) and TP is the corresponding truncated path.
% The tail of the path is valid - it has been extended at the front (by a
% data constructor and/or a ref) and this is where folding may have to take
% place to make the whole path valid. We may have to keep the first data
% constructor or ref and fold the second one with the start of the valid
% path or fold the single dc or ref with the start of the valid path or we
% might not need to do any folding at all.  Eg: (with [..] around folded
% bits)
% ._ref.cons/2.2 -> ._ref.cons/2.2 (no folding)
% [.cons/2.2].cons/2.2 -> .cons/2.2
% [.cons/2.2].cons/2.1 -> .cons/2.1
% ._ref[.cons/2.2].cons/2.1.t2/2.2 -> ._ref.cons/2.1.t2/2.2
% .leaf[.cons/2.2].cons/2.1.t2/2.2 -> .leaf.cons/2.1.t2/2.2
% [.r2rc1.r2rc2._ref].r2rc1.r2rc2 -> .r2rc1.r2rc2
% [.r1rrc._ref._ref].r1rrc._ref -> .r1rrc._ref
fold_type_path(T, P, TP) :-
    type_struct(T, TS),
    fold_type_path_sum(TS, P, TP).

% as above for sum type representation
% New path must be a valid path of type TS, must have the same non-empty
% suffix (TPC) and the same prefix (TPA) but missing a (possibly empty)
% chunk in the middle (_TPB).  We want the longest such path(?), and rely on
% the order of answers returned by app_vpc XXX - hmm, currently we use two
% calls to app_vpc, the first returns the longest instance of TPBC first
% and the second 
fold_type_path_sum(TS, P, TP1) :-
    % previous version - NQR
    once((
    app_vpc(TPA, TPBC, P),      % longest TPBC first
    app_vpc(_TPB, TPC, TPBC),    % longest TPC first
    TPC \= vpe,
    app_vpc(TPA, TPC, TP),
    type_path_sum(TS, [], TP, varf, _PInfo)
    )),
    % Older: This coding uses backtracking and commits to the first solution
    % - relies on app_vpc returning the longest path first XXX YUK re-code
%     once((
%     app_vpc(TP, _, P),
%     type_path_sum(TS, [], TP, varf, _PInfo)
%     )),
    TP1 = TP.

% we want to remove (fail here) sharing of Var if Arity=0 or the
% DC/Arity don't match the path
% Note that for recursive types we have to be careful.  For example, for
% binary trees with data in leaves, DC branch/2 matches leaf/1 because
% (with current precision of paths) the args of branch/2 are sum_ref_anc
% nodes which are the same as the empty path. The type struct is passed
% in.
% Easiest to express negatively..
% Maybe fix this so we use var paths as noted somewhere?
% XX does it really have to be this complicated?/can we refactor?
% XXXXX check with new path code with no _ref made explicit etc ZZZ
alias_var_dcons_ok(Var, TS, DC, Arity, SP) :-
    \+ alias_var_dcons_to_rm(Var, TS, DC, Arity, SP).

% Succeeds if we want to drop this alias pair
alias_var_dcons_to_rm(Var, _TS, _DC, 0, s(vp(Var, _), _)).
alias_var_dcons_to_rm(Var, _TS, _DC, 0, s(_, vp(Var, _))).
alias_var_dcons_to_rm(Var, TS, DC, Arity, s(vp(Var, vpc(DC1, Arity1, _, _)), _)) :-
    \+ ( DC = DC1, Arity = Arity1 ),
    \+ has_ref_anc(TS, DC, Arity).
alias_var_dcons_to_rm(Var, TS, DC, Arity, s(_, vp(Var, vpc(DC1, Arity1, _, _)))) :-
    \+ ( DC = DC1, Arity = Arity1 ),
    \+ has_ref_anc(TS, DC, Arity).

% check if DC/Arity is in type with recursion to node at or above this
% DC/Arity.  Eg for branch/2 its true.
% May succeed more than once (but we only call this inside \+)
% XXXX problem with some builtin types, including ref. Even with
% rectype.pns this fails for ref/1.  Best pass type in also if possible
% - most refs should be ok, even when we have some types with recursion
% through ref/1.  Uses type_struct_c which is only the cached types -
% may not include all relevant types. type_struct can be called with
% non-ground types but vars get instantiated to ref(void) so it can't be
% used as a generator here.
has_ref_anc(sum(_T, Prods), DC, Arity) :-
    Prod = prod(DC, Arity, Sums),
    member(Prod, Prods),
    member(Sum, Sums),
    has_ref_anc_sum(Sum, 2).

% type has reference to ancestor >= D
has_ref_anc_sum(sum_ref_anc(_, N), D) :-
    N >= D.
has_ref_anc_sum(sum_ref(_, sum(_, Sums)), D) :-
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
rename_vars([], _,  _, []).
rename_vars([PV^DU|PVs], FAs, Args, [V1^DU|Vs]) :-
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
    add_typed_anns(S, S1, VTm0, VTm, [], _PolyVs),
    smash_type_vars(S1), % XX?
    % add_last_anns not needed but last_use anns could speed things up
    add_last_anns(S1, S2, last(_), [], _UVs, [], _IBVs),
    alias_stat(S2, VTm, [], SS).

% XX function declarations currently asserted rather than being passed
% around: just fname and canonical type stored
:- dynamic(nfdec_struct/2).

% XX declarations with "inferred" postconditions stored here temporarily
:- dynamic(nfdec_struct_inferred_post/2).

% XX function definitions currently asserted rather than being passed
% around
% fn_def_struct(Fn, Args, Stat, VTm),
:- dynamic(fdef_struct/4).

fn_def_struct(A, B, C, VTm) :- fdef_struct(A, B, C, VTm).

%%%%%%
% Overall handling of statements for sharing analysis
% XXX should remove alias info from dead vars some time - thats what
% last_use is designed for
% Second arg here and related preds is Var-Type map for statement, which
% we need just when folding types for vars that have paths that share
% with LHS of := (not used in some of preds)
alias_stat(C-_Ann, _VTm, SS0, SS) :-
    C = empty_stat, % not needed?
    SS = SS0.
alias_stat(C-_Ann, VTm, SS0, SS) :-
    C = seq(Sa, Sb),
    alias_stat(Sa, VTm, SS0, SS1),
    alias_stat(Sb, VTm, SS1, SS).
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = eq_var(Vl, Vr),
    VPl = vp(Vl, vpe),
    VPr = vp(Vr, vpe),
    alias_stat_veq(VPl, VTm, VPr, Ann, SS0, SS),
    % if Vr has different type to Vl we have a cast and if there is
    % any sharing introduced between these vars we must not implicitly
    % mutate Vr later
    % XXXX add this check to DC and applications also (or everything)
    % XPOLY Casts now not needed much (?) - if Vr is mutated later with a more
    % instantiated type, the type of Vr (and Vl) will be further instantiated
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
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = eq_deref(Vl, Vr),
    VPl = vp(Vl, vpe),
    VPr = vp(Vr, vpc('_ref', 1, 1, vpe)),
    alias_stat_veq(VPl, VTm, VPr, Ann, SS0, SS).
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = deref_eq(Vl, Vr),
    VPl = vp(Vl, vpc('_ref', 1, 1, vpe)),
    VPr = vp(Vr, vpe),
    alias_stat_veq(VPl, VTm, VPr, Ann, SS0, SS).
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = assign(Vl, Vr),
    member(typed(T), Ann),
    % type_struct(T, Sum),
    VPl = vp(Vl, vpc('_ref', 1, 1, vpe)),
    % VPr = vp(Vr, vpe),
    findall(BV, member(bang(_, BV), Ann), Bs),
    check_banged_lhs(VPl, Bs, SS0, Ann, (*Vl := Vr), VTm), % IO
    % find self-sharing (existing) components of RHS
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
    add_sharing_for_lhs_aliases(T, VTm, VPl, LVPs, AVPs, [], SSNew2),
    sort(SSNew2, SSNew3),
    sharing_union(SSNew3, SSRHS, SS).
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = var_stat(V),
    ( member(last_stat, Ann) ->
        alias_stat(eq_var(returnvar, V)-Ann, VTm, SS0, SS)
    ;
        SS = SS0
    ).
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = cases(V, Cases),
    member(typed(T), Ann),
    map(alias_stat_case(V, VTm, T, SS0), Cases, SSs),
    foldr(ord_union, [], SSs, SS). % XX balanced fold is better
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = eq_dc(V, DC, Arity, Args),
    ( Args = [] -> % optimise case for constants
        SS = SS0
    ;
        member(typed(T), Ann),
        map('X,vp(X,vpe)', Args, DCAs),
        type_struct(T, TDSum),
        % XXX hmm can fail if prev type checking failed
        % maybe we should not attempt sharing analysis if type checking
        % fails
        TDSum = sum(_, TDProds),
        member(prod(DC, Arity, ASums), TDProds),
        alias_stat_dc(V, VTm, ASums, TDSum, DC, Arity, 1, DCAs, SS0, SSN),
        sort(SSN, SSNew),
        sharing_union(SSNew, SS0, SS)
    ).
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = eq_app(V, Fn, Args),
    % we are applying a variable which might be a closure.  We don't
    % know (yet) if it returns a closure (see note in eq_sapp case)
    alias_stat_app(V, VTm, Fn, Args, Ann, SS0, SSN),
    length(Args, Arity),
    member(typed(T), Ann),
    ( T = arrow(_,_,_,_,_,_,_,_,_,_,_) ->
        renumbered_closure_arg_sharing(Arity, Fn, V, SS0, SSN3)
    ;
        SSN3 = SS0
    ),
    sort(SSN3, SSN4),
    sharing_union(SSN4, SSN, SSN1),
    sharing_union(SSN1, SS0, SS).
alias_stat(C-Ann, VTm, SS0, SS) :-
    C = eq_sapp(V, Fn, Args),
    % known saturated app: currently we only get this for known fns (not
    % vars which might be closures), so its a bit simpler.  Potentially
    % type analysis could pick up some cases where applications of vars
    % are known to be saturated (this would result in more efficient
    % compiled code).  If so, we may need a more general case here.
    alias_stat_app(V, VTm, Fn, Args, Ann, SS0, SSN),
    sharing_union(SSN, SS0, SS).
alias_stat(C-Ann, VTm, SS0, SS) :-
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
        alias_stat_app(V, VTm, Fn, Args, Ann, SS0, SSN),
        sharing_union(SSN, SS0, SS)
    ).

% case for application of fns/vars with args - return new sharing.
% Fn can be a constant or a variable.
alias_stat_app(V, VTm, Fn, Args, Ann, SS0, SSN) :-
    member(typed_rhs(RType), Ann),
    length(Args, Arity),
    LVP = vp(V, vpe),
    map('X,vp(X,vpe)', Args, AVPs),
    findall(BV, member(bang(_, BV), Ann), Bs),
    arrow_to_sharing_dus(Arity, RType, RFAs, Pre, APost, DUDUs, _, RWDUIs1, WOIs1),
    map(strip_duspec, RWDUIs1, RWIs1),
    map(strip_duspec, DUDUs, DUs),
    RFAs = [R|FAs],
    % we only need to keep sharing info for result and DU args
    % (including implicit rw and wo)
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
    RType = arrow(_, _, _, _, _, _, _, CLATs, ROIs, RWDUIs, WOIs),
    map(strip_duspec, RWDUIs, RWIs),
    append(ROIs, RWIs, RORWIs),
    map('X,vp(X,vpe)', ROIs, ROVPs),
    map('X,vp(X,vpe)', RWIs, RWVPs),
    map('X,vp(X,vpe)', WOIs, WOVPs),
    length(CLATs, NCL),
    % CLMin is Arity + 1,
    % CLMax is CLMin + NCL - 1,
    CLMin is 1,
    CLMax is NCL,
    % CLMax is CLMin + NCL - 2, % XXX right?
    % XXX currently get extra cla's for LHS (V) Should somehow use actual
    % arity of function (length(RFAs)-1?) not just supplied args
    % and current closure args???
    % mk_closure_var_paths(CLMin, CLMax, V, CLFnPs, _SSSC),
    mk_closure_var_paths(CLMin, CLMax, Fn, CLFnPs, _SSSC),
%     length(RFAs, NRFA),
%     ND is NRFA - 1 - Arity - NCL,
%     length(Dummies, ND), % need at least ND dummies; could have more
%     map0(=(vp('_dummy',vpe)), Dummies),
    % append([[LVP], CLFnPs, AVPs], ResArgs),
    % % map('X,vp(X,vpe)', CLFnVs, CLFnPs),
    % % append(CLFnVs, Args, AArgs), % just want vars, not paths
    append(CLFnPs, AVPs, AArgs),
    % rename_sharing ignores sharing between vars which are not renamed
    % so we have to explicitly include implicit args, which are renamed
    % to themselves (XX maybe rethink this)
    append([FAs, ROIs, RWIs], FAs1),
    append([AArgs, ROVPs, RWVPs], AArgs1),
    rename_sharing(Pre, FAs1, AArgs1, PreSS),
    sort(PreSS, PreSS1),
    % Bs has duspecs for each var, from bang() annotations.
    % DUs, DUVs, AllDUs don't but we get their annotations from
    % DUDUs+RWDUIs.  check_banged needs the annotations
    map('X,vp(X,_)', CLFnVs, CLFnPs),
    append(CLFnVs, Args, AArgVs), % just want vars, not paths
    rename_vars(DUDUs, FAs, AArgVs, DUVs),
    append(RWDUIs, DUVs, AllDUs),
    check_banged(Bs, AllDUs, SS0, Ann, (LVP = app(Fn, AVPs)), VTm), % IO
    % we include abstract with var for type so it matches any type
    % (but we check later the type is not void)
    append([[vp(abstract(AbsType),vpe)], ROVPs, RWVPs, AVPs], AllVPs),
    (   member(S, SS0),
        S = s(SVP1, SVP2),
        SVP1 \= SVP2, % ignore self-sharing
        SVP1 = vp(V1, P1),
        SVP2 = vp(V2, P2),
        % check if both vars in sharing pair are relevant to call
        % or one is relevant and it aliases a state var that is not in
        % the call
        ( member(vp(V1, _), AllVPs) -> % V1 relevant to call
            ( member(vp(V2, _), AllVPs) -> % V2 relevant to call
                AbsType \== void, % ignore bogus sharing with abstract(void)
                % we generalise abstract so any type/path can match
                gen_abstract(SVP1, SVP3),
                gen_abstract(SVP2, SVP4),
                \+ member(s(SVP3, SVP4), PreSS1),
                print('Error: precondition violation:'(app(Fn, AVPs), S)),
                nl,
                write_src(Ann)
            ; aliased_sv(V2, P2) ->
            \+ member(V1, RORWIs),
                writeln('Error: aliased state var must be implicit rw/ro:'(Fn, V2, V1))
            )
        ;
            aliased_sv(V1, P1),
            member(vp(V2, _), AllVPs),
            \+ member(V2, RORWIs),
            writeln('Error: aliased state var must be implicit rw/ro:'(Fn, V1, V2))
        ),
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

% var is a state var and path has just a single ref
aliased_sv(V, vpc('_ref', 1, 1, vpe)) :-
    state_var(V, _).

% path with just ref
ref_path(vpc('_ref', 1, 1, vpe)).

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
    % avoid repeated solutions YYY no longer needed
    once(fold_type_path(T, vpc('_ref', 1, 1, RP), LP)).

% make self-alias
self_alias(VP, s(VP, VP)).

% make alias pair from var, path, and var path
alias_var(Vr, Pr, LVP, S) :-
    mk_alias_pair(LVP, vp(Vr, Pr), S).

% given ancestor type, remove ref() wrapper from type or replace
% sum_ref_anc(2) by ancestor
strip_ref_type(_, sum_ref(_, T), T).
strip_ref_type(Anc, sum_ref_anc(_, 2), Anc).

% alias_stat for (possibly deref) var equality
alias_stat_veq(VPl, _VTm, VPr, Ann, SS0, SS) :-
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
    ( VPr = vp(_, vpc('_ref', 1, 1, _)) ->
        RT = ref(T)
    ;
        RT = T
    ),
    ( VPr = vp(abstract(TA), vpe) ->
        % for abstract sharing, find all paths for the type (we assume
        % each component of abstract exists) then create all the sharing
        % pairs (that includes self sharing for abstract)
        type_paths(TA, RPs),
        rpath_aliases(RPs, RT, VPr, LSum, VPl, SSN)
    ;
        findall(RP, var_path_shared(SS0, VPr, RP), RPs),
        rpath_aliases(RPs, RT, VPr, LSum, VPl, SSN)
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
        % Path = vpc('_ref', _, _, Path1), % will always be a ref in path
        Path1 = Path, % no longer will always be a ref in path
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
% abstract(maybe(int)) is used as a fake variable that may share with any
% maybe(int) component of an abstract var. Note we could potentially
% avoid abstract sharing for atomic types but currently include it so
% x=abstract; y=abstract results in all components of x and y sharing.
% XXX re-think and document all the cases here - has been modified a bit
% with new type paths/folding regime
% XXXX for cases r of { case dc(... *l ...) ...} we are missing the case
% where the extra path for l is empty.  
rpath_aliases([], _, _, _, _, []).
rpath_aliases([P|Ps], RT, VPr, LSum, VPl, Ss) :-
    VPl = vp(Vl, Pl),
    VPr = vp(Vr, Pr),
    app_vpc(Pr, P, Pr1),
    % compute path for l, if it exists (use maybe): MPl
    ( Pr = vpe ->
        app_vpc(Pl, P, Pl1),
        fold_type_path_sum(LSum, Pl1, Pl2), % should always succeed
        MPl = just(Pl2)
    ;
        % either eq_deref: l = *r
        % or eq_case: cases r of { case dc(... *l ...) ...}
        % type of r has eg _ref() wrapper and this might result in more
        % folding, like r._ref.cons/2.2 folded to r._ref.  We need to undo
        % the folding to construct the l.cons/2.2 path to share it with
        % We do this by generating paths for Pl until we find one that,
        % when prefixed with dc (or _ref), folds to the path we want
        % Best to encapsulate this inverse of type folding (might need
        % it elsewhere also - see paper on sharing analysis)
        % Note: this may fail if the type of l is atomic and thus has no
        % paths (r has one path with a single ref). Thus we use a maybe to
        % return the new path for l.
        % XXXX with new abs domain r._ref.cons/2.2 *isn't* folded to r._ref
        % When VPl = vp(Vl, vpc(_ref,1,1,vpe)) we are losing the alias
        % with this path
        Pr = vpc(DC, Arity, ArgN, _),
        app_vpc(Pr, P, Pr1),
        sum_to_type(LSum, LT),
        ( Pl = vpc('_ref', 1, 1, vpe) ->
            app_vpc(Pl, P, Pl1),
            fold_type_path_sum(LSum, Pl1, Pl2), % XX should succeed?
            MPl = just(Pl2)
        % XXX check this works for nested arrow types?
        % XXXX and anything else...
        ; (type_path_sum(LSum, [], Pl1, vpef, _PInfo),
            fold_type_path(ref(LT), vpc(DC, Arity, ArgN, Pl1), Pr1))
        ->
            MPl = just(Pl1)
        ;
            MPl = nothing
        )
    ),
    ( MPl = just(Pl3) ->
        % print(rpath_aliases(Vl, RT, N, Pr1, Pl1, Pl3)), nl,
        % for abstract we need to fix the type and include
        % self-aliasing for abstract of that type
%         ( Vr = abstract(T) ->
%             Pr2 = vpe,
%             Vr1 = abstract(T1),
%             path_type_map(Pr1, T, T1),
%             ( atomic_type(T1) ->
%                 Ss = [S2|Ss1]
%             ;
%                 mk_alias_pair(vp(Vr1, vpe), vp(Vr1, vpe), SSSAS),
%                 Ss = [SSSAS, S1, S2|Ss1]
%             )
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
%XXX Vl wrong below; need
% app_vpc(Pl, P, Pl1) + fold
        mk_alias_pair(vp(Vl, Pl3), vp(Vr1, Pr2), S1),
        mk_alias_pair(vp(Vl, Pl3), vp(Vl, Pl3), S2) % self-alias
    ;
        Ss = Ss1
    ),
    rpath_aliases(Ps, RT, VPr, LSum, VPl, Ss1).

'X,vp(X,vpe)'(X,vp(X,vpe)).

'X,vp(X,_)'(X,vp(X,_)).

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
% XXX potential extra work to handle duspec on rw properly - currently
% duspec is put on definition of state var so it's the same for all
% functions that use it (making HO type checking easier) but if this
% changes the code here may need fixing
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
        ord_subtract(RPostSS1, LPostSS1, DiffPostSS),
        print('   extra sharing'(DiffPostSS)),
        nl,
        write_src(Anns)
    ),
    % check mutable args: R should be subset of L
    % XXXXX need to rename first!
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
% XXXX add stuff to handle cyclic terms + ??sharing between args
% case var of ... dcons(...) ->
% Need to add aliases for paths within var + ags of dcons.
% We know the data constructor for this var, so we can filter out
% other data constructors for this var from the current alias set in
% some cases. Have to be careful of folding though: eg, if dcons is
% branch/2 and we have sharing in a leaf component of var we *can't*
% delete the sharing because a branch/2 term can have leaf components
% within it (paths starting with leaf/1 can represent subterms of terms
% with branch/2 at the top level). We can't remove sharing with a data
% constructor that has a ref_anc node, pointing back to the data
% constructor or something above it. For leaf/1 we *can* remove branch/2
% sharing, for nil we can remove cons sharing and for left/1 we can
% remove right/1 (and vice versa).
% Not sure what following means (must ave a typo somewhere):
% Best use var path rather than var?
% Can we do the following at some stage?: if we have a var xs which
% is (x:xs1) and x is true and xs is [], all the aliasing of *xs* should
% be deleted (x and xs1 should be a var path starting with x rather than
% separarate vars, maybe).
% Worth looking at some examples to consider precision XX
alias_stat_case(Var, VTm, T, SS0, case_dc(DC, Arity, As, S), SS) :-
    type_struct(T, TS),
    filter(alias_var_dcons_ok(Var, TS, DC, Arity), SS0, SS1),
    TS = sum(_, Ps),
    % XXX should check DC is well typed in type checking
    ( member(prod(DC, Arity, Sums), Ps) ->
        eq_case_args(As, Sums, TS, 1, Var, DC, Arity, SS0, SSN),
        sort(SSN, SSN1),
        sharing_union(SSN1, SS1, SS6)
    ;
        writeln('Error: ill-typed case: '(DC, Arity, T)),
        SS6 = SS0
    ),
    alias_stat(S, VTm, SS6, SS).

% 'X,var(X)'(X,var(X)).
% 'X,var(X)'(X,vp(X,vpc('_ref',1,1,vpe))).

% given args, arg num and var path + data constructor/arity from case,
% create alias pairs for var components and args (which must be *var)
eq_case_args([], _, _, _, _, _, _, _, []).
eq_case_args([Vr|As], [Sum|Sums], LSum, A, Vl, DC, Arity, SS0, SSN) :-
    % construct path for argument and top level alias
    Pl1 = vpc(DC, Arity, A, vpe),
    VPl = vp(Vl, Pl1),
    VPr = vp(Vr, vpc('_ref', 1, 1, vpe)),
    mk_alias_pair(VPl, VPr, S),  % *Vr aliases arg of Vl
    mk_alias_pair(VPr, VPr, S1), % self-alias
    % For the longer paths we call rpath_aliases and we use the type of
    % the argument. The case type is sum(_,[prod([Sum|Sums])...]) and we
    % look for the type inside Sum and reconstruct the sum (RSum)
    % because it may have been folded.
    arg(1, Sum, TSN), % Sum is sum_ref_anc(TSN, 2) or sum_ref(TSN, _)
    type_struct(TSN, RSum),
    findall(LP, var_path_shared(SS0, VPl, LP), LPs),
    % could move this earlier
    ( LPs = [] ->
        writeln('  Warning: unreachable case:'(DC/Arity))
    ;
        true
    ),
    % left and right a bit confusing - in rpath_aliases left is the new
    % var being bound and right is the existing var; for case the new
    % vars being bound are textually after the existing var, eg
    % cases l of {case dc(*r)} is like *r = dcarg(l)
    sum_to_type(LSum, RT),
    rpath_aliases(LPs, RT, VPl, RSum, VPr, SSN1),
    append(SSN1, [S, S1|SSN2], SSN),
    A1 is A + 1,
    eq_case_args(As, Sums, LSum, A1, Vl, DC, Arity, SS0, SSN2).

% eq_dc handling
% XXXX do we miss adding sharing between different paths for
% Vl if different VPr's share???
% YES- BUG, eg see sa(*xp=1; p=t2(xp,xp))
alias_stat_dc(_, _VTm, _, _, _, _, _, [], _, []).
alias_stat_dc(Vl, VTm, [ASum|ASums], LSum, DC, Arity, A, [VPr|Args], SS0, SSN) :-
    findall(RP, var_path_shared(SS0, VPr, RP), RPs),
    % Pl1 = vpc(DC, Arity, A, vpc('_ref', 1, 1, vpe)),
    Pl1 = vpc(DC, Arity, A, vpe),
    % we may also need to fold path for Vl ???
    % - shouldn't be necessary now because empty paths are avoided
    ( fold_type_path_sum(LSum, Pl1, Pl1T) ->
        Pl2 = Pl1T
    ;
        writeln('Huh? fold_type_path_sum failed in alias_stat_dc'(LSum, Pl1)),
        Pl2 = Pl1
    ),
    VPl = vp(Vl, Pl2),
    mk_alias_pair(VPl, VPl, S), % self-alias
    sum_to_type(ASum, RT),
    rpath_aliases(RPs, RT, VPr, LSum, VPl, SSN1),
    append(SSN1, [S|SSN2], SSN),
    A1 is A + 1,
    alias_stat_dc(Vl, VTm, ASums, LSum, DC, Arity, A1, Args, SS0, SSN2).

%%%%%%
% Overall handling of function definitions
% XX failure driven loop...
alias_fn(Fn) :-
    writeln('    sharing analysis of '(Fn)),
    nfdec_struct(Fn, T),
    % We replace type vars by fudged ground param types that have a
    % single component for sharing no data constructors
    smash_type_params(T),
    func_arity(Fn, Arity),
    arrow_to_sharing_dus(Arity, T, RFAs, Precond, Postcond, BDUArgs, ROIs, RWDUIs, WOIs),
    map(strip_duspec, RWDUIs, RWIs),
    % map(strip_duspec, BDUArgs, BArgs),
    fn_def_struct(Fn, Args, Stat, VTm),
    %
    % check all args which are banged in definition are banged in
    % declaration XX could delete if types are annotated with purity
    banged_vars(Stat, DUs),
    map('X,vp(X,vpe)', AVs, Args),
    % we use setof to avoid duplicate error messages
    (   setof(Msg, ND^DUSB^DUSA^ (
            member(ND, AVs),              % var ND is an argument
            member(ND^DUSB, DUs),         % and is DU in fn body
            ( member(ND^DUSA, BDUArgs) -> % it's declared DU in type sig
                \+ duspec_subsumes(DUSA, DUSB),
                Msg = 'Error: argument should be declared more mutable: '(ND,DUSA, DUSB)
            ;
                Msg = 'Error: argument should be declared mutable: '(ND)
            )
            ), Msgs),
        % note wo implicit args are handled like other vars because
        % currently their duspecs are added to each instance automatically
        % XXX What if state vars have explicit duspecs added - could
        % check they are compatible (currently disallow)
        member(Msg, Msgs),
        writeln(Msg),
        fail
    ;
        true
    ),
    % XXX delete following once above works
%     sort(DUs, SDUs),
%     sort(AVs, SArgs),
%     sort(BArgs, SBArgs),
%     ord_intersection(SDUs, SArgs, DUArgs),
%     ord_subtract(DUArgs, SBArgs, NDs),
%     ( setof(ND, (   member(ND^_, DUs),
%                     member(ND, AVs),
%                     \+ member(ND^_, DUArgs)), NDs) ->
%         % NDs \= []
%         writeln('Error: argument(s) should be declared mutable: '(NDs))
%     ;
%         true
%     ),
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
        \+ state_var(IV, _),
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
    % nfdec_struct(Fn, TFn), % do we need to call this again?? YY
    % smash_type_params(TFn),
    TFn = T,
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
% print(yyx(SSelfs)), nl,
    ( alias_stat(Stat, VTm, SSI2, SS) ->
        % need to check for sharing between args+result which is not
        % declared in postcondition
        % also need to check for state vars which are introduced locally by
        % calling a WO function aliasing with args+result; currently we
        % over-approximate by considering all state vars which are not
        % implicitly returned XXXXXX NQR if we have local var with the same
        % name (should ban/warn about this! Also affects alias_stat_app)
        findall(SV, (state_var(SV, _),
                    \+ member(SV, RFAs1)
                    ), SVs),
        member(S, SS),
        S = s(VP1, VP2),
        VP1 = vp(V1, P1),
        VP2 = vp(V2, P2),
        V1 \= V2,   % XX ignore self aliasing - should include later?
        ( memberchk(vp(V1, _), ResArgs1) ->
            ( memberchk(vp(V2, _), ResArgs1) ->
                \+ member(S, PostSS2),
                print('Error: postcondition violated:'(Fn, VP1, VP2)),
                nl
            ;
                memberchk(V2, SVs),
                ref_path(P2),
                % best remove trailing ref from path etc
                print('Error: illegal post-alias with state variable:'(Fn, VP1, VP2)),
                nl
            )
        ;
            memberchk(vp(V2, _), ResArgs1),
            memberchk(V1, SVs),
            ref_path(P1),
            % best remove trailing ref from path etc
            print('Error: illegal post-alias with state variable:'(Fn, VP2, VP1)),
            nl
        )
    ;
        write('Oops! alias_stat failed!'),
        nl
    ),
    % writeln('sharing at end'(SS)),
    fail.
alias_fn(_).

% Design for more precise DU analysis (duspec/DU specification):
% Banged vars now of the form v^duspec, where duspec specifies which
% components may be updated.  We want an expressive duspec language that
% (preferably) doesn't depend on the abstract domain. Current version is
% an expression containing ! at various points, meaning var paths that match
% the outer duspec down to that point may be du (others are not).
% ! - du if path empty
% dc(s1,s2) where s1 & s2 are duspecs - paths starting dc/2.1 (or dc/2.2) then
% rest of path matches s1 (or s2, respectively)
% ? - place holder for dc args we are not interested in
% ...s1 - any path followed by match for s1 (... defined as prefix op)
% s1/s2 - paths matching with s1 or s2
% !s1 - du if path empty or matches s1 (need ! as prefix op) (??? see below)
% Maybe add a more refined version of ... that only allows some dc/arg
% combinations - useful for (eg) lists of lists where we want to
% distinguish du of inner vs outer lists. Maybe add ::type after ! to
% constrain du to arg of that type? Currently we don't have type info
% passed in/used but it would be useful for extra precision anyway.  Could
% have problems with operator precedence of :: and ! used as prefix
% operator (don't strictly need !s1 - can always use !/s1 instead so maybe
% delete it? XXX).
% !::t - du if path empty and subterm has type t
% Could also potentially add
% !::type_of(v) to support polymorphism better (would need to pass in VTm
% rather than just a single type, or process duspecs after type checking)
% Examples:
% ...! = any subterm DU (default for !var with no duspec)
% dc(!,?,!) = first and third args of dc at top level are DU
% ref(!) = special case of above, for LHS of *!v := ...
% ...dc(!,?,!) = first and third args of dc at lowest level
% dc1(!)/dc2(!,?) = first arg of dc1 or dc2 at top level
% dc1(!dc2(!,?),?) = first args of dc1 + dc2 as first arg of dc1
% or dc1(!/dc2(!,?),?) instead of above
% dc1(!/ ...dc2(!,?),?) = first args of dc1 + d2 anywhere in first arg of dc1
% ...cons(!::int, ?) = first arg of any cons cell that is type int
% ...cons(!::list(int), ?) = first arg of any cons cell that is type list(int)
% 
% XXX should be able to have !,?,/ etc as data constructors in duspecs
% - maybe we could use ? / f(...) to mean f is to be used as a data
% constructor (rather than duspec builder), even if f is !,?,/ etc
%
% Note: initial dupsec support was for explicit arguments (plus vars
% in statements to check argument duspecs are correct).  It can also
% be useful for state variables.  State variable declarations
% can now have a duspec (and/or potentially we could use explicit duspecs
% where implicit rw args are defined - not done).  The latter is less
% important - only useful where there is sharing between state vars and
% other vars with abstract components and in some context we need better
% precision.  It also complicates HO type checking.
% For the former (duspec on SV definitions) allow state vars with abstract
% components (these can't be updated by the wrappers can). We need
% to check the duspecs on a rw state var within a function definition are
% subsumed by the duspec on the state var definition.  For state var
% definitions we use (eg) (XXX should have ref explicit for consistency?)
% !gcoords^ ...cons(!,!) :: list(pair(int,int)).
% meaning gcoords^ref(!/ ...cons(!,!)) - outermost ref is always du and
% here each arg of any cons is du but the pairs are not du.  For wo
% functions we allow any du of the var - it can always be eliminated
% by using a temporary var and assigning that to the state var at the end
% (could possibly give warning/error instead).

% check if first duspec is (definitely) more general than second
% (ie, du subterms of first spec is a superset of second)
% XXX stub - best extend this, though it's not *so* important currently
% as we don't infer duspec annotations on ! vars in statements and the
% specs for DU of args should really just reflect those in statements
% Messy, may succeed multiple times; need to be careful of non-termination.
% XXX uses expand_du_spec at top level only - better to allow at all
% levels of term and apply when src is read rather than here.
% XX could this be more precise with type info?
duspec_subsumes(DUS1, DUS2) :-
    expand_du_spec(DUS1, DUS3),
    expand_du_spec(DUS2, DUS4),
    duspec_subsumes1(DUS3, DUS4).

% as above without expand_du_spec
duspec_subsumes1(DUS, DUS).
duspec_subsumes1(...!, _).
duspec_subsumes1(_, ?).
duspec_subsumes1(!, !).
duspec_subsumes1(!_, !). % XXX delete?
duspec_subsumes1(!::T1, !::T2) :-
    % XXX should do canon_type_name just once, before this
    canon_type_name(T1, T),
    canon_type_name(T2, T).
duspec_subsumes1(!DUS1, !DUS) :-
    duspec_subsumes1(DUS1, DUS).
duspec_subsumes1(!DUS1, DUS) :-
    duspec_subsumes1(DUS1, DUS).
duspec_subsumes1(DUS, DUS1/DUS2) :-
    \+ ( slash_member(DUS2, DUS1/DUS2),    % each member of DUS1/DUS2
        \+ ( slash_member(DUS3, DUS),      % has a member of DUS
            duspec_subsumes1(DUS3, DUS2))  % that subsumes it
    ).
duspec_subsumes1(DC1, DC2) :-
    functor(DC1, F, N),
    functor(DC2, F, N),
    F \= '/',
    F \= '...',
    F \= !,
    F \= ?,
    DC1 =.. [F|As1],
    DC2 =.. [F|As2],
    map(duspec_subsumes1, As1, As2).

% checks if duspec *definitely* allows DU for a given var path
% Note it is imprecise - may be paths that have ! but this fails.
% eg, du_spec_vpc_def_bang(cons(?,!), list(int), vpc(cons, 2, 2, vpe))
% fails (due to type folding, the actual path may have several cons
% cells; the duspec only covers the case where there is a single cons
% cell. If we use ...cons(?,!) instead, the duspec covers all cases so
% du_spec_vpc_def_bang(...cons(?,!), list(int), vpc(cons, 2, 2, vpe))
% succeeds.
du_spec_vpc_def_bang(DUS, Type, VPC) :-
    expand_du_spec(DUS, DUS1),
    type_struct(Type, ST),
    once(du_spec_vpc_def_bang1(DUS1, ST, VPC)). % avoid multiple solns

% as above with expand_du_spec done
du_spec_vpc_def_bang1(!, _ST, vpe).
du_spec_vpc_def_bang1(!_, _ST, vpe). % XXX delete?
du_spec_vpc_def_bang1(!::T, ST, vpe) :-
    % XXX should do canon_type_name just once, before this
    arg(1, ST, T1),
    canon_type_name(T, T1).
du_spec_vpc_def_bang1(!DUS, ST, VPC) :-
    du_spec_vpc_def_bang1(DUS, ST, VPC).
du_spec_vpc_def_bang1(DUS/_, ST, VPC) :-
    du_spec_vpc_def_bang1(DUS, ST, VPC).
du_spec_vpc_def_bang1(_/DUS, ST, VPC) :-
    du_spec_vpc_def_bang1(DUS, ST, VPC).
du_spec_vpc_def_bang1(...DUS, ST, VPC) :-
   % Top level match.  If DUS is a data constructor there is overlap
   % with the next clause.  However, this clause covers the cases where
   % DUS is ! or / etc
   du_spec_vpc_def_bang1(DUS, ST, VPC).
du_spec_vpc_def_bang1(...DUS, ST, VPC) :-
    % strip data constructor in path and continue
    VPC = vpc(F, N, A, VPC1),
    % we extract the arg type and recompute the sum to avoid any problems
    % with folding (could avoid this in some cases)
    ( F = '_ref', N = 1 ->
        ST = sum_ref(ref(T1), _)
    ;
        ST = sum(_, Prods),
        member(prod(F, N, SRs), Prods),
        nth1(A, SRs, SumRef), % SumRef is sum_ref or sum_ref_anc
        arg(1, SumRef, ref(T1))
    ),
    type_struct(T1, ST1),
    du_spec_vpc_def_bang1(...DUS, ST1, VPC1).
du_spec_vpc_def_bang1(DUS0, ST, VPC) :-
    % match outermost data constructor of DUS0 and path then continue
    % recursively with arg.
    % For recursive types that might be folded, we fail *unless
    % we have a ... wrapper* (more overlap between clauses but we need
    % to have different handling of data constructors depending on
    % wheather they are inside ... due to folding)
    ( DUS0 = (...DUS) ->
        Dots = true
    ;
        DUS = DUS0,
        Dots = false
    ),
    VPC = vpc(F, N, A, VPC1),
    F \= '!', % XXX should be able to have ! etc as DC in duspecs
    F \= '/',
    F \= '...',
    F \= ?,
    ( DUS = ref(_) ->
        ST = sum_ref(ref(T1), _),
        F = '_ref',
        N = 1
    ;
        functor(DUS, F, N),
        ST = sum(_, Prods),
        member(prod(F, N, SRs), Prods),
        nth1(A, SRs, SumRef), % SumRef is sum_ref or sum_ref_anc
        arg(1, SumRef, ref(T1))
    ),
    type_struct(T1, ST1),
    % if there are multiple data constructors in the type and
    % ST1 has a sum_ref_anc node that points back to before ST1
    % VPC may be folded due to recursion in type and top level
    % term may not be F/N, so we should fail without ... wrapper
    \+ (dots = false, Prods \= [_], has_ref_anc(ST, F, N)),
    % VPC term must have F/N (at top level if no ...) so continue with arg A
    arg(A, DUS, DUS1),
    ( Dots = true ->
        DUS2 = (... DUS1)
    ;
        DUS2 = DUS1
    ),
    du_spec_vpc_def_bang1(DUS2, ST1, VPC1).

% checks if duspec *possibly* allows DU for a given var path
% XXX imprecise - may be paths that have no ! but this succeeds
% eg, du_spec_vpc_poss_bang(cons(?,!), list(int), vpc(cons, 2, 2, vpe))
% succeeds (due to type folding, the actual path may have several cons
% cells; the duspec only covers the case where there is a single cons
% cell.
% XXX best use type at some point so we can deal with folding better.
du_spec_vpc_poss_bang(DUS, Type, VPC) :-
    expand_du_spec(DUS, DUS1),
    type_struct(Type, ST),
    once(du_spec_vpc_poss_bang1(DUS1, ST, VPC)). % avoid multiple solns

% as above with expand_du_spec done
du_spec_vpc_poss_bang1(!, _ST, vpe).
du_spec_vpc_poss_bang1(!::T, ST, vpe) :- % XXX need types
    % XXX should do canon_type_name just once, before this
    canon_type_name(T, T1),
    arg(1, ST, T1). % XXX for sum_ref we have a ref wrapper
du_spec_vpc_poss_bang1(!_, _ST, vpe). % XXX delete?
du_spec_vpc_poss_bang1(!DUS, ST, VPC) :- % XXX delete?
    du_spec_vpc_poss_bang1(DUS, ST, VPC).
du_spec_vpc_poss_bang1(DUS/_, ST, VPC) :-
    du_spec_vpc_poss_bang1(DUS, ST, VPC).
du_spec_vpc_poss_bang1(_/DUS, ST, VPC) :-
    du_spec_vpc_poss_bang1(DUS, ST, VPC).
du_spec_vpc_poss_bang1(...DUS, ST, VPC) :-
    app_vpc(_, VPC1, VPC),
    du_spec_vpc_poss_bang1(DUS, ST, VPC1).
du_spec_vpc_poss_bang1(DUS1, ST, VPC) :-
    ( DUS1 = ref(_) -> % convert ref/1 to '_ref/1'
        ST = sum_ref(_, ST1),
        F1 = '_ref',
        N = 1
    ;
        functor(DUS1, F, N),
        F \= '!',
        F \= '/',
        F \= '...',
        F \= ?,
        F1 = F
    ),
    % vpc(F1, N...) could be anywhere in path due to folding
    % XXX! currently we only enforce F1/N at the top level for types
    % with no recursion.  Best also check there are multiple data
    % constructors in the type (if there is just one it is OK)
    app_vpc(VPC2, vpc(F1, N, A, VPC1), VPC),
    arg(A, DUS1, DUS2),
    ( has_ref_anc(ST, F1, N) ->
        % XXXX! should compute type ST1 from ST+path and
        % recurse. Not done yet so we just succeed
        % du_spec_vpc_poss_bang1(DUS2, ST1, VPC1)
        true
    ;
        % XXX possibly not tested
        VPC2 = vpe,
        ST = sum(_, Prods),
        member(prod(F, N, SRs), Prods),
        nth1(A, SRs, sum_ref(ref(_), ST1)),
        du_spec_vpc_poss_bang1(DUS2, ST1, VPC1)
    ).

% return members of A1/A2/A3 etc
slash_member(A, AS) :-
    ( AS = AS1/AS2 ->
        (   slash_member(A, AS1)
        ;
            slash_member(A, AS2)
        )
    ;
        A = AS
    ).

% for !V^DUS in statement, check if V is a state var and if so, that DUS
% is compatible with state var declaration
check_duspec_on_state_var(V, DUS, Stat) :-
    ( state_var(V, DUS1), \+ duspec_subsumes(DUS1, DUS) ->
        writeln('ERROR: incompatible duspec on state variable '(V)),
        write_src([src(Stat)])
    ;
        true
    ).

% get banged vars in stat
banged_vars(S, Vs) :-
    banged_vars_1(S, [], Vs1),
    sort(Vs1, Vs). % remove duplicates

% as above with accumulator
banged_vars_1(C-Ann, Vs0, Vs) :-
    ( C = seq(S1, S2) ->
        banged_vars_1(S1, Vs0, Vs1),
        banged_vars_1(S2, Vs1, Vs2)
    ; C = cases(_, Cs) ->
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
banged_vars_case(case_dc(_, _, _, S), Vs0, Vs) :-
    banged_vars_1(S, Vs0, Vs).
banged_vars_case(case_def(S), Vs0, Vs) :-
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
% Defflag inserted/checked also
lookup_old_assoc(Key, Assoc, Value, NewAssoc) :-
    ( get_assoc(Key, Assoc, Value-DF) ->
        NewAssoc = Assoc,
        ( (DF = def ; checking_pre_post) ->
            true
        ;
            % writeln(Assoc),
            writeln('Error: possibly undefined variable '(Key))
        )
    ;
        ( checking_pre_post ->
            true
        ;
            writeln('Error: undefined variable '(Key)),
            writeln(Assoc)
            % XXXX can lead to major barf - should protect where this is
            % called
        ),
        put_assoc(Key, Assoc, Value-undef, NewAssoc)
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

alias_fn(list_bst_du).

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

% precision with non-recursive types versus recursive
sa(t = true; b = just(t); c = nothing; *x = b).
sa(t = true; b = just(t); c = nothing; *x = b; *x := c).
sa(t = true; b = cons(t, nil); c = nil; *x = b).
sa(t = true; b = cons(t, nil); c = nil; *x = b; *x := c).

% required type unfolding for c = *b
sa(a = cons(true, nil); *b = a; c = *b).
sa(a = cons(true,nil); cases a of {nil: true case cons(*b,*c): false}).



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

spy(alias_stat).
spy(in_as).
spy(xxx).
spy(arrow_to_sharing_dus).
/^alias_stat

spy(rm_unshared_var_ref_aliases).
sa(*zp = 42; *wp = 43;    *yp = zp;    *xp = yp;    *yp := wp).

retractall(tdef(T, D)), builtin_tdef(T, D), assert(tdef(T, D)), fail.
retractall(nfdec_struct(Fn1, T)), builtin_fdec((Fn :: ST)), fdec_fdec_struct(Fn, ST, Fn1, T), assert(nfdec_struct(Fn1, T)), fail.
retractall(func_arity(Fn, Arity)), builtin_func_arity(Fn, Arity), assert(func_arity(Fn, Arity)), fail.

% missing s(p.t2/2.1._ref._ref,p.t2/2.2._ref._ref) ???
sa(*xp=1; p=t2(xp,xp)).

alias_stat(eq_var(x,abstract(list(pair(int, int))))- [typed(list(pair(int, int)))], [], SS), print(SS), fail.


san('../examples/cord.pns').
san('cord.pns').
sa(l = cons(true, nil); c = leaf(l)).
sa(l = cons(true, nil); c = branch(leaf(nil), leaf(l))).
% XXX s(c.leaf.cons/2.1,l.cons/2.1) missing???
% XXX plus s(c.leaf.cons/2.1,c.leaf.cons/2.1)
sa(c0 = leaf(nil)).
sa(c0 = leaf(nil); c = branch(c0, leaf(nil))).
sa(l = cons(true, nil); cl = leaf(l); a = leaf(nil)).
sa(l = cons(true, nil); cl = leaf(l); a = leaf(nil); x = branch(a, cl)).
% 


type_struct(r2, S), trunc_type_path_sum(S, P, N), writeln(P).
type_paths(r3, Ps).
sa(a = r1z; b = r1c(a); c = r1c(b)).
sa(a = r2z; b = r2c2(a); r=r2c1(b)).
type_paths(cb, P).

san('rectype.pns').
san('testuf.pns').
san('eval.pns').
san('wam.pns').
san('isort.pns').
san('bst_poly.pns').
san('bst1.pns').
san('cord.pns').
san('cord_poly.pns').
san('ho.pns').
san('bst.pns').
san('bst_a.pns').
san('pbst.pns').
san('p1bst.pns').
san('bst_poly.pns').
san('testq.pns').
san('map.pns').
san('testq.pns').
san('state.pns').

spy(alias_stat).
spy(alias_stat_veq).

T = ref(cb), type_struct(T, TS), type_path_sum(TS, [], P, vpef, PInfo).
alias_fn(find).
alias_fn(main1).

fdef_fdef_struct1(main1(v), seq(seq(eq_sapp('V0', q_empty, [v])-[],
eq_var(q, 'V0')-[src(q= (q_empty(v)::queue(int))), typed(pair(list(int),
ref(list(int))))])-[src(q= (q_empty(v)::queue(int))),
typed(pair(list(int), ref(list(int))))], seq(eq_dc('V1', void, 0,
[])-[src(void)], var_stat('V1')-[src(void)])-[src(void)])-[],

fdef_struct(main1, [vp(v, vpe)], seq(seq(
eq_sapp('V0', q_empty,
[v])-[ibanged_later([]), last_use([]), used_later(['V0', 'V1', io, v]),
wo[],
% XXX ref(void) below
typed(pair(list(ref(void)), ref(list(ref(void))))),
typed_rhs(arrow(void, pair(list(ref(void)), ref(list(ref(void)))), [],
[v], q, nosharing, nosharing, [], [], [], []))],
eq_var(q, 'V0')-[ibanged_later([]), last_use(['V0']), used_later(['V1', io, v]),
typed(pair(list(int), ref(list(int)))), typed_rhs(pair(list(int),
ref(list(int)))), casts(['V0']), src(q= (q_empty(v)::queue(int))),
typed(pair(list(int), ref(list(int))))])
-[src(q= (q_empty(v)::queue(int))), typed(pair(list(int), ref(list(int))))],

seq(eq_dc('V1', void, 0, [])-[ibanged_later([]), last_use([]),
used_later(['V1', io, v]), typed(void), typed_rhs(void), src(void)],
var_stat('V1')-[last_stat, ibanged_later([]), last_use(['V1']),
used_later([io, v]), typed(void), typed_rhs(void),
src(void)])-[src(void)])-[], t(returnvar, (void sharing main1(v)pre
nosharing post nosharing)-def, <, t('V1', void-def, -, t('V0',
pair(list(ref(void)), ref(list(ref(void))))-def, -, t, t), t(q,
pair(list(int), ref(list(int)))-def, -, t, t)), t(v, void-def, -, t,
t))))

% XXX fails due du '_type_param'(1) vs ref??
add_sharing_for_lhs_aliases('_type_param'(1), t(b, ref('_type_param'(2))-def, >,
t(a, ref('_type_param'(1))-def, -, t, t), t(returnvar, void-def, -, t(n,
'_type_param'(1)-def, -, t, t), t(t, pair('_type_param'(1), '_type_param'(2))-def,
-, t, t))), vp(a, vpc('_ref', 1, 1, vpe)), [vp(a, vpc('_ref', 1, 1,
vpc('_type_param', 1, 1, vpe)))], [vp(t, vpc(t2, 2, 1, vpe)),
vp(abstract('_type_param'(1)), vpe)], [], _G10795).
add_sharing_for_lhs_aliases1('_type_param'(1), t(b, ref('_type_param'(2))-def, >,
t(a, ref('_type_param'(1))-def, -, t, t), t(returnvar, void-def, -, t(n,
'_type_param'(1)-def, -, t, t), t(t, pair('_type_param'(1), '_type_param'(2))-def,
-, t, t))), vp(a, vpc('_ref', 1, 1, vpc('_type_param', 1, 1, vpe))),
vpc('_type_param', 1, 1, vpe), [vp(t, vpc(t2, 2, 1, vpe)),
vp(abstract('_type_param'(1)), vpe)], [], _G10795)

XXXX
san('bst.pns').
spy(add_typed_anns_dcapp).
sa(xs = cons(1,nil); *tp = mt; foldl_du(xs,bst_insert_du,!tp)).

san('duspec.pns').
san('state.pns').
[pawns].
[pawns,comp].
['../pawns.pl', '../comp.pl'].
['../compiler/pawns.pl', '../compiler/comp.pl'].
['../compiler/pawns.pl'].
prolog
*/
ct :- retractall(type_struct_c(_,_)).
x :- spy(xxx).
as :- spy(alias_stat).
aa :- spy(alias_stat_app).
ac :- spy(alias_stat_case).
ar :- spy(arrow_to_sharing_dus).
at :- spy(add_typed_anns).
t :- trace.
% p :- [pawns].
p :- ['../compiler/pawns.pl'].


