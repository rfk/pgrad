
:- module domain.

:- interface.

:- type agent ---> harriet ; thomas ; richard.
:- type object == string.

:- type time == int.
:- type duration == int.

:- type task ---> mix(object,duration) ; chop(object).

:- pred task_duration(agent::in,task::in,duration::out) is det.

:- implementation.

task_duration(_,mix(_,D),D).
task_duration(Agt,chop(_),D) :-
    if Agt=harriet
    then D=5
    else D=3.

