
:- dynamic(indi_exog/1).
:- dynamic(currently/2).
:- dynamic(temp/2).

:- set_flag(all_dynamic,on).

:- [golog].
:- [domain].

retractall(H) :-
    retract_all(H).

% printFluentValues(+FluentList, +History): Print value of primitive fluents
%     at the point where History actions have been performed
printFluentValues([], _) :-
    write('-----------------------------------------------'),
    nl.

printFluentValues([Hf | FluentList], History) :-
    write('    Primitive fluent '),
    write(Hf),
    write(' has value '),
    has_val(Hf, Hv, History),
    write(Hv), nl,
    printFluentValues(FluentList, History).


