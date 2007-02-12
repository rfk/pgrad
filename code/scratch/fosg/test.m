
:- module test.

:- interface.
:- import_module io.

:- pred main(io::di,io::uo) is det.


:- implementation.
:- import_module fosg.
:- import_module list.
:- import_module int.

main(!IO) :-
    A = fosg.mkgraph(fosg.mkkernel(func("hello",[])),t,f),
    B = fosg.mkgraph(fosg.mkkernel(func("there",[])),t,f),
    C = fosg.mkgraph(fosg.mkkernel("hello",A),B,f),
    J = fosg.not(C),
    io.print(fosg.mkgraph(fosg.mkkernel("hello",A),t,t),!IO),
    io.write_string("\n",!IO).
