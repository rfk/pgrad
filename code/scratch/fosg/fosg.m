
:- module fosg.

:- interface.

:- import_module list.
:- import_module term.

:- type graph ---> t ; f ; sh(kernel,graph,graph).
:- type kernel ---> s(string) ; g(list(var),graph).

:- type fof ---> fof `and` fof
              ; fof `or` fof
              ; fof `imp` fof
              ; fof `eqv` fof
              ; ~ fof.

:- pred shgraph(kernel::in,graph::in,graph::in,graph::out) is det.

:- implementation.

% TODO: pragma memo
shgraph(Kernel,TGraph,FGraph,sh(Kernel,TGraph,FGraph)).


