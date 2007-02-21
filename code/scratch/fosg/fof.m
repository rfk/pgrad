%
%  Module for manipulating first-order formulae.
%

:- module fof.

:- interface.
:- import_module list.
:- import_module string.

% First-Order Formulae are an abstract type
:- type fof.

% Terms can either be variables, ordinary functions, or
% "unique" functions.  The later basically serve as canonical
% names for objects, and are treated according to unique names
% axioms of the form:
%
%     ufunc(S1,A1)=ufunc(S2,A2)  iff S1=S2 and A1=A2
%
:- type term ---> var(string)
                ; func(string,list(term))
                ; ufunc(string,list(term))
                .

:- type subst == list({term,term}).

% Basic functions for constructing formulae from simpler formulae.
%
:- func atom(string,list(term)) = fof.
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

:- pred tautological(fof::in) is semidet.
:- pred contradictory(fof::in) is semidet.


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- implementation.

% We represent formulae as shannon graphs. Each node has a kernel.
% a true edge and a false edge.  There are also the leaf nodes t and f.
% 
:- type fof == sgraph.
:- type sgraph ---> t ; f ; ite(kernel,sgraph,sgraph).

% Node kernels are either an atom or a quantified subgraph.
%
:- type kernel ---> p(string,list(term)) ; q(list(string),sgraph).

:- type prover_state ---> prv(
                               bindings :: subst,
                               pos_atoms :: list(kernel),
                               neg_atoms :: list(kernel),
                               u_quants :: list(kernel),
                               e_quants :: list(kernel)
                          ).

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

%  Prune away branches that are obviously dead.
%  Basically, don't follow any branches containing a kernel
%  whose sign has already been decided higher in the path.
%
:- func prune(sgraph) = sgraph.
:- func prune(list(kernel),list(kernel),sgraph) = sgraph.

prune(G1) = G :-
    prune([],[],G1) = G.

prune(_,_,t) = t.
prune(_,_,f) = f.
prune(PathT,PathF,ite(K1,T,F)) = G :-
    (if K1 = q(Vars,FQ) then
        K = mkkernel_q(Vars,prune(FQ))
    else
        K = K1),
    (if list.member(K,PathT) then
        G = prune(PathT,PathF,T)
    else
        if list.member(K,PathF) then
            G = prune(PathT,PathF,F)
        else
            G = mkgraph(K, prune(list.cons(K,PathT),PathF,T),
                           prune(PathT,list.cons(K,PathF),F))).


:- func prover_state_init = prover_state.
prover_state_init = PS :-
    PS ^ bindings = [],
    PS ^ pos_atoms = [],
    PS ^ neg_atoms = [],
    PS ^ u_quants = [],
    PS ^ e_quants = [].

%  Attempt to close all t-paths in the graph.
%  This is a theorem-prover for first-order logic.
%
:- pred close_paths(sgraph::in,prover_state::in,prover_state::out) is nondet.

close_paths(t,!PS) :- fail.
close_paths(f,!PS).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%  Implement fof functions in terms of sgraph functions

atom(Name,Args) = F :-
    F = mkgraph(mkkernel_p(Name,Args),t,f).

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

tautological(_).
contradictory(_).

