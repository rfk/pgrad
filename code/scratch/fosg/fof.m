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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- implementation.

% We represent formulae as shannon graphs. Each node has a kernel.
% a true edge and a false edge.  There are also the leaf nodes t and f.
% 
:- type fof == sgraph.
:- type sgraph ---> t ; f ; ite(kernel,sgraph,sgraph).

% Node kernels are either an atom or a quantified subgraph.
%
:- type kernel ---> p(term) ; q(list(string),sgraph).

% For structure-sharing purposes, use these functions to construct
% the various types of object.  We use pragma memo to ensure sharing.
%
:- func mkgraph(kernel,sgraph,sgraph) = sgraph.
:- func mkkernel(term) = kernel.
:- func mkkernel(list(string),graph) = kernel.

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


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%


:- pragma memo(mkgraph/3,[addr,addr,addr,output]).
all(Vars,Graph1) = Graph :-
    Graph = mkgraph(/mkgraph

mkgraph(Kernel,TGraph,FGraph) = G :-
    if TGraph = FGraph then
        G = TGraph
    else
        G = ite(Kernel,TGraph,FGraph).

:- pragma memo(mkkernel/1,[value,output]).
mkkernel(Term) = p(Term).

:- pragma memo(mkkernel/2,[value,addr,output]).
mkkernel(Vars,Graph) = q(Vars,Graph).

:- pragma memo(replace/2,[addr,value,output]).
replace(Graph,RepL) = GraphP :-
    if firstmatch(Graph,Repl,NG) then
        GraphP = NG
    else
        Graph = ite(K,T,F),
        GraphP = mkgraph(K,replace(T,RepL),replace(F,RepL))
        ;
        Graph = t, GraphP = t
        ;
        Graph = f, GraphP = f.

%  Implement FOF functions in terms of replace/2
%
and(Graph1,Graph2) = Graph :-
    Graph = replace(Graph1,[{t,Graph2}]).
or(Graph1,Graph2) = Graph :-
    Graph = replace(Graph1,[{f,Graph2}]).
not(Graph1) = Graph :-
    Graph = replace(Graph1,[{f,t},{t,f}]).
impl(Graph1,Graph2) = Graph :-
    Graph = replace(Graph1,[{f,t},{t,Graph2}]).
equiv(Graph1,Graph2) = Graph :-
    Graph = replace(Graph1,[{f,not(Graph2)},{t,Graph2}]).
all(Vars,Graph1) = Graph :-
    Graph = mkgraph(mkkernel(Vars,Graph1),t,f).
exists(Vars,Graph1) = Graph :-
    Graph = mkgraph(mkkernel(Vars,not(Graph1)),f,t).


