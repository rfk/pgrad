
:- module main.

:- interface.
:- import_module io.

:- pred main(io::di,io::uo) is det.

:- implementation.
:- import_module domain.

main(!IO) :-
    (
        task_duration(harriet,chop("lettuce"),D),
        io.write_string("Duration: ",!IO),
        io.write_int(D,!IO),
        io.write_string("\n",!IO)
    ).

