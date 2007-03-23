%
%  Module for manipulating first-order formulae.
%

:- module fof.

:- interface.
:- import_module list.
:- import_module string.
:- import_module io.

% First-Order Formulae are an abstract type
:- type fof.
:- pred tester(io::di,io::uo) is det.

% Terms can either be variables, ordinary functions, or
% "unique" functions.  The later basically serve as canonical
% names for objects, and are treated according to unique names
% axioms of the form:
%
%     ufunc(S1,A1s)=ufunc(S2,A2s)  iff  S1=S2 and A1s=A2s
%
:- type term ---> var(string)
                ; func(string,list(term))
                ; ufunc(string,list(term))
                .

:- type subst == list({term,term}).

% Basic functions for constructing formulae from simpler formulae.
%
:- func atom(string,list(term)) = fof.
:- func natom(string,list(term)) = fof.
:- func not(fof) = fof.
:- func and(fof,fof) = fof.
:- func or(fof,fof) = fof.
:- func impl(fof,fof) = fof.
:- func equiv(fof,fof) = fof.
:- func all(list(string),fof) = fof.
:- func exists(list(string),fof) = fof.

% Do some basic simplifications on a FOF
%
:- func simplify(fof) = fof.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- implementation.

:- import_module map.


% We represent formulae as shannon graphs. Each node has a kernel,
% a true edge and a false edge.  There are also the leaf nodes t and f.
% 
:- type fof == sgraph.
:- type sgraph ---> t ; f ; ite(kernel,sgraph,sgraph).

% Node kernels are either an atom or a quantified subgraph.
%
:- type kernel ---> p(string,list(term)) ; q(list(string),sgraph).


% For structure-sharing purposes, use these functions to construct
% the various types of object.  We use pragma memo to ensure sharing.
%
:- func mkgraph(kernel,sgraph,sgraph) = sgraph.
:- func mkkernel_p(string,list(term)) = kernel.
:- func mkkernel_q(list(string),sgraph) = kernel.

:- pragma memo(mkgraph/3,[addr,addr,addr,output]).
mkgraph(Kernel,TGraph,FGraph) = G :-
    if TGraph = FGraph then
        G = TGraph
    else
        G = ite(Kernel,TGraph,FGraph).

:- pragma memo(mkkernel_p/2,[value,value,output]).
mkkernel_p(Name,Args) = p(Name,Args).

:- pragma memo(mkkernel_q/2,[value,addr,output]).
mkkernel_q(Vars,Graph) = q(Vars,Graph).


% The most basic operation on graphs is simultaneous replacement
% of nodes with other nodes.
%
:- func replace(sgraph,list({sgraph,sgraph})) = sgraph.

:- pred firstmatch(sgraph::in,list({sgraph,sgraph})::in,sgraph::out) is semidet.
firstmatch(Target,[{G1,G2}|Tail],Out) :-
    if Target = G1 then
        Out = G2
    else
        firstmatch(Target,Tail,Out).

:- pragma memo(replace/2,[addr,value,output]).
replace(Graph,RepL) = GraphP :-
    if firstmatch(Graph,RepL,NG) then
        GraphP = NG
    else
        Graph = ite(K,T,F),
        GraphP = mkgraph(K,replace(T,RepL),replace(F,RepL))
        ;
        Graph = t, GraphP = t
        ;
        Graph = f, GraphP = f.

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
%  Some useful datatypes and predicates for exploring a shannon graph.
%

%  A collection of atoms encountered so far.  For fast access
%  to likely unification candidates, we map first by the predicate
%  name, then by its arity.

:- type atom_set == map(string,map(int,list(list(term)))).

:- func atom_set_init = atom_set.
atom_set_init = Atoms :- map.init(Atoms).

:- func atom_set_search(atom_set,string,int) = list(list(term)).
atom_set_search(Atoms,Pred,Arity) = ArgsList :-
    if map.search(Atoms,Pred,PMap) then
      (if map.search(PMap,Arity,AList) then
        ArgsList = AList
      else
        ArgsList = [])
    else
      ArgsList = [].

:- pred atom_set_contains(atom_set::in,string::in,list(term)::in) is semidet.
atom_set_contains(Atoms,Pred,Args) :-
    AList = atom_set_search(Atoms,Pred,list.length(Args)),
    list.member(Args,AList).

:- func atom_set_insert(atom_set,string,list(term)) = atom_set.
atom_set_insert(Atoms0,Pred,Args) = Atoms1 :-
    list.length(Args,Arity),
    (if map.search(Atoms0,Pred,PMap) then
        (if map.search(PMap,Arity,AList) then
            map.det_update(PMap,Arity,[Args | AList],PMap1),
            map.det_update(Atoms0,Pred,PMap1,Atoms1)
         else
            map.det_insert(PMap,Arity,[Args],PMap1),
            map.det_update(Atoms0,Pred,PMap1,Atoms1)
        )
     else
        map.init(PMap),
        map.det_insert(PMap,Arity,[Args],PMap1),
        map.det_insert(Atoms0,Pred,PMap1,Atoms1)
     ).


%  Record information about things that were encountered along
%  a path through the graph.

:- type path_info ---> path(pos_atoms :: atom_set,
                            neg_atoms :: atom_set,
                            u_kerns :: list(kernel),
                            e_kerns :: list(kernel)).

:- func path_info_init = path_info.
path_info_init = PI :-
    PI ^ pos_atoms = atom_set_init,
    PI ^ neg_atoms = atom_set_init,
    PI ^ u_kerns = [],
    PI ^ e_kerns = [].

:- func path_info_add_pos(path_info,kernel) = path_info.
:- func path_info_add_neg(path_info,kernel) = path_info.
path_info_add_pos(PI,q(Vars,SubG)) =
    PI ^ u_kerns := ([q(Vars,SubG)|PI ^ u_kerns]).
path_info_add_pos(PI,p(Pred,Args)) =
    PI ^ pos_atoms := atom_set_insert(PI ^ pos_atoms,Pred,Args).
path_info_add_neg(PI,q(Vars,SubG)) =
    PI ^ e_kerns := ([q(Vars,SubG)|PI ^ e_kerns]).
path_info_add_neg(PI,p(Pred,Args)) =
    PI ^ neg_atoms := atom_set_insert(PI ^ neg_atoms,Pred,Args).


%  Test for simple truthity or falsehood of kernels on a particular path.

:- pred true_on_path(kernel::in,path_info::in) is semidet.
true_on_path(q(Vars,SubG),PathInfo) :-
    list.member(q(Vars,SubG),PathInfo ^ u_kerns).
true_on_path(p(Pred,Args),PathInfo) :-
    trivially_true(Pred,Args) ; 
    atom_set_contains(PathInfo ^ pos_atoms,Pred,Args).

:- pred false_on_path(kernel::in,path_info::in) is semidet.
false_on_path(q(Vars,SubG),PathInfo) :-
    list.member(q(Vars,SubG),PathInfo ^ e_kerns).
false_on_path(p(Pred,Args),PathInfo) :-
    trivially_false(Pred,Args) ; 
    atom_set_contains(PathInfo ^ neg_atoms,Pred,Args).


% Detect trivial truthity or falsehood based solely on the atom.
% This basically encodes our special handling of the "=" predicate.

:- pred trivially_true(string::in,list(term)::in) is semidet.
:- pred trivially_false(string::in,list(term)::in) is semidet.

trivially_true("=",[X,X]).

trivially_false("=",[ufunc(N1,A1s),ufunc(N2,A2s)]) :-
    list.length(A1s,A1n), list.length(A2s,A2n),
    (if (N1 \= N2 ;A1n \= A2n) then
        true
     else
        TF = (pred(Args::in) is semidet :- trivially_false("=",Args)),
        ArgKerns = list.chunk(list.zip(A1s,A2s),2),
        list.filter(TF,ArgKerns,FalseKerns),
        list.is_not_empty(FalseKerns)
    ).


%  Prune away branches that are obviously dead.
%  Basically, don't follow any branches containing a kernel
%  whose sign has already been decided higher in the path.
%
:- func prune(sgraph) = sgraph.
:- func prune(path_info,sgraph) = sgraph.

prune(G1) = G :-
    prune(path_info_init,G1) = G.

prune(_,t) = t.
prune(_,f) = f.
prune(PathInfo,ite(K1,T,F)) = G :-
    (if K1 = q(Vars,FQ) then
        K = mkkernel_q(Vars,prune(FQ))
    else
        K = K1),
    (if true_on_path(K,PathInfo) then
        G = prune(PathInfo,T)
     else
       (if false_on_path(K,PathInfo) then
           G = prune(PathInfo,F)
        else
           G = ite(K, prune(path_info_add_pos(PathInfo,K),T),
                      prune(path_info_add_neg(PathInfo,K),F))
       )
    ).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%
%  Predicates for exploring all paths of a shannon graph,
%  e.g. to test for closure.
%

:- type search_result ---> open ; closed ; unknown.

:- type search_state ---> ss( path :: path_info,
                       patom_data :: int,
                       natom_data :: int,
                       ukern_data :: int,
                       ekern_data :: int,
                       call_on_t :: pred(in,out) is multi,
                       call_on_f :: pred(in,out) is multi,
                       depth_limit :: int,
                       result :: search_result
                      ).


:- pred explore_paths(sgraph::in,search_state::in,search_state::out) is multi.

explore_paths(t,SSi,SSo) :-
    call(SSi ^ call_on_t,SSi,SSo).

explore_paths(f,SSi,SSo) :-
    call(SSi ^ call_on_f,SSi,SSo).

%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%  Implement fof functions in terms of sgraph functions

atom(Name,Args) = F :-
    F = mkgraph(mkkernel_p(Name,Args),t,f).

natom(Name,Args) = F :-
    F = mkgraph(mkkernel_p(Name,Args),f,t).

not(F1) = F :-
    F = replace(F1,[{f,t},{t,f}]).

and(F1,F2) = F :-
    F = replace(F1,[{t,F2}]).

or(F1,F2) = F :-
    F = replace(F1,[{f,F2}]).

impl(F1,F2) = F :-
    F = replace(F1,[{f,t},{t,F2}]).

equiv(F1,F2) = F :-
    F = replace(F1,[{f,not(F2)},{t,F2}]).

all(Vars,F1) = F :-
    F = mkgraph(mkkernel_q(Vars,F1),t,f).

exists(Vars,F1) = F :-
    F = mkgraph(mkkernel_q(Vars,not(F1)),f,t).

simplify(F1) = F :-
    F = prune(F1).
    % TODO: other simplifications, such as reducing scope of quants

tester(!IO) :-
    G1 = fof.atom("=",[func("ryan",[]),func("lauren",[])]),
    G2 = fof.atom("=",[func("twin",[ufunc("one",[])]),func("twin",[func("two",[])])]),
    Go = fof.prune(fof.or(G1,G2)),
    io.write(Go,!IO).
