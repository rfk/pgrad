
:- module test.

:- interface.
:- import_module io.

:- pred main(io::di,io::uo) is det.

:- implementation.
:- import_module fosg.

main(!IO) :-
    A = fosg.shgraph(s("hello"),t,f),
    B = fosg.shgraph(s("hello2"),t,f),
    io.write_string("success!",!IO).
