%
%  First-Order Shannon Graphs
%
%

:- module fosg.

:- interface.
:- import_module list.
:- import_module string.

% A first-order shannon graph is basically a tree with two
% terminal nodes, identified by t and f.

:- type graph ---> t ; f ; sh(kernel,graph,graph).


% The kernel of the graph is either a f.o. proposition, or
% a quantified subgraph (of a single variable).

:- type kernel ---> p(term) ; q(string,graph).


% Terms are basically functors applied to arguments.

:- type term ---> func(string,list(term)).

% For structure-sharing purposes, use these functions to construct
% the various types of object.

:- func mkgraph(kernel,graph,graph) = graph.
:- func mkkernel(term) = kernel.
:- func mkkernel(string,graph) = kernel.

% The basic operations on a shannon graph:
%   replace instances of subgraphs
%   prune away dead branches

:- func replace(graph,list({graph,graph})) = graph.
:- func prune(graph) = graph.


% Higher-level boolean operations.

:- func and(graph,graph) = graph.
:- func or(graph,graph) = graph.
:- func not(graph) = graph.

:- implementation.

:- pragma memo(mkgraph/3,[addr,addr,addr,output]).
mkgraph(Kernel,TGraph,FGraph) = G :-
    if TGraph = FGraph then
        G = TGraph
    else
        G = sh(Kernel,TGraph,FGraph).

:- pragma memo(mkkernel/1,[value,output]).
mkkernel(Term) = p(Term).

:- pragma memo(mkkernel/2,[value,addr,output]).
mkkernel(Str,Graph) = q(Str,Graph).

:- pragma memo(replace/2,[addr,value,output]).
replace(Graph,RepL) = GraphP :-
    if (promise_equivalent_solutions [NG] list.member({Graph,NG},RepL)) then
        GraphP = NG
    else
        Graph = sh(K,T,F),
        GraphP = mkgraph(K,replace(T,RepL),replace(F,RepL))
        ;
        Graph = t, GraphP = t
        ;
        Graph = f, GraphP = f.


prune(Graph) = Graph.

and(Graph1,Graph2) = Graph :-
    Graph = replace(Graph1,[{t,Graph2}]).
or(Graph1,Graph2) = Graph :-
    Graph = replace(Graph1,[{f,Graph2}]).
not(Graph1) = Graph :-
    Graph = replace(Graph1,[{f,t},{t,f}]).


