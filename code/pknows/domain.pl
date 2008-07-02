

:- discontiguous(causes_true/3).
:- discontiguous(causes_false/3).

% Enumerate the values of the various types in the domain
agent(ann).
agent(bob).

location(c).
location(d).

result(R) :-
  location(R).

observation(nil).
observation(A) :-
    action_with_vars(A,Vs),
    enumerate_vars(Vs).
observation(pair(A,R)) :-
    action_with_vars(A,Vs),
    enumerate_vars(Vs),
    result(R).

object(O) :-
    agent(O) ; location(O) ; result(O) ; observation(O).

% Enumerates primitive actions, and the types of their arguments.
prim_action(read(agent)).
prim_action(leave(agent)).
prim_action(enter(agent)).

% Enumerates primitive fluents, and types of arguments
prim_fluent(loc(location)).
prim_fluent(inroom(agent)).

% Enumerates conditions for action description predicate fluents
adp_fluent(poss,read(Agt),inroom(Agt)).
adp_fluent(poss,enter(Agt),~inroom(Agt)).
adp_fluent(poss,leave(Agt),inroom(Agt)).

adp_fluent(canObs(Agt),read(_),inroom(Agt)).
adp_fluent(canObs(_),leave(_),true).
adp_fluent(canObs(_),enter(_),true).

adp_fluent(canSense(Agt),read(Agt2),Agt=Agt2).
adp_fluent(canSense(_),leave(_),false).
adp_fluent(canSense(_),enter(_),false).

adp_fluent(sr(R),read(_),loc(R)).
adp_fluent(sr(ok),leave(_),true).
adp_fluent(sr(ok),enter(_),true).

%  Specify what holds in the initial situation.
%
initially(loc(c)).
initially(inroom(ann)).
initially(inroom(bob)).
initially(knows(ann,inroom(ann) & inroom(bob))).
initially(knows(bob,inroom(ann) & inroom(bob))).
initially(~ ?([L^location] : knows(ann,loc(L)))).
initially(~ ?([L^location] : knows(bob,loc(L)))).

% Causal rules for each fluent/action combo
causes_true(inroom(Agt),enter(Agt2),(Agt=Agt2)).
causes_false(inroom(Agt),leave(Agt2),(Agt=Agt2)).


:- begin_tests(domain).

test(reg1) :-
    regression(inroom(ann),read(bob),inroom(ann)).
test(reg2) :-
    regression(inroom(ann),enter(bob),inroom(ann)).
test(reg3) :-
    regression(inroom(ann),leave(bob),inroom(ann)).
test(reg4) :-
    regression(inroom(ann),enter(ann),true).
test(reg5) :-
    regression(inroom(ann),leave(ann),false).


test(adp1) :-
    adp_fluent(canObs(ann),read(ann),inroom(ann)).
test(adp2) :-
    adp_fluent(canObs(ann),read(bob),inroom(ann)).

test(holds1) :-
    holds(inroom(ann),s0), !.
test(holds2,fail) :-
    holds(~inroom(ann),s0).
test(holds3) :-
    holds(~inroom(ann),do(leave(ann),s0)), !.
test(holds4) :-
    holds(inroom(ann),do(leave(bob),s0)), !.
test(holds5) :-
    holds(?([X^agent] : inroom(X)),do(leave(bob),s0)), !.
test(holds6) :-
    holds(!([X^agent] : inroom(X)),s0), !.
test(holds7) :-
    \+ holds(!([X^agent] : inroom(X)),do(leave(bob),s0)).
test(holds8) :-
    holds(loc(c),s0), !.


test(knows1) :-
    holds(knows(ann,inroom(ann)),s0), !.
test(knows2) :-
    holds(knows(ann,inroom(bob)),s0), !.
test(knows3) :-
    holds(knows(bob,~inroom(ann)),do(leave(ann),s0)), !.
test(knows4) :-
    holds(~knows(bob,inroom(ann)),do(leave(ann),s0)), !.
test(knows5) :-
    holds(~knows(bob,loc(c)),s0), !.


test(example1) :-
    holds(~ ?([L^location]:knows(ann,loc(L))),s0), !.
test(example2) :-
    holds(knows(bob,loc(c)),do(read(bob),s0)), !.
test(example3) :-
    holds(knows(bob,~ ?([L^location]:knows(ann,loc(L)))),s0).
test(example4) :-
    holds(~ knows(bob,~ ?([L^location]:knows(ann,loc(L)))),do(leave(bob),s0)).

:- end_tests(domain).

