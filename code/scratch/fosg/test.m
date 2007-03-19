
:- module test.

:- interface.
:- import_module io.

:- pred main(io::di,io::uo) is det.


:- implementation.
:- import_module fof.
:- import_module list.

main(!IO) :-
    A = fof.atom("likes",[fof.ufunc("Mary",[]),fof.ufunc("John",[])]),
    B = fof.atom("likes",[fof.ufunc("John",[]),fof.ufunc("Jane",[])]),
    C = fof.and(A,fof.not(B)),
    D = fof.and(C,C),
    io.print(D,!IO),
    io.write_string("\n",!IO),
    io.print(fof.simplify(D),!IO),
    io.write_string("\n",!IO).

