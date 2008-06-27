

:- discontiguous(causes_true/3).
:- discontiguous(causes_false/3).


agent(ann).
agent(bob).

location(c).
location(d).

result(R) :-
  location(R).

observation(nil).
observation(A) :-
    is_prim_action(A).
observation(A^R) :-
    is_prim_action(A), result(R).

% Enumerates primitive actions, and the domains of their arguments.
prim_action(read(agent)).
prim_action(leave(agent)).
prim_action(enter(agent)).

% Enumerates primitive fluents, and domains of arguments
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

% Enumerates the fluents holding in the initial situation.
% Rather than using negation-as-failure, we explicitly specify all literals
% known to be true and known to be false.  This allows the initial database
% to model (common) incomplete knowledge.
%
initially_true(inroom(ann)).
initially_true(inroom(bob)).
initially_true(loc(c)).

initially_false(loc(d)).

initially_knownT(inroom(ann)).
initially_knownT(inroom(bob)).

initially_knownF(_) :- fail.


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
test(knows3) :-
    holds(~knows(bob,inroom(ann)),do(leave(ann),s0)), !.
test(knows4) :-
    holds(~knows(bob,loc(c)),s0), !.


%test(example1) :-
%    holds(~?([L:location]:knows(ann,loc(L))),s0).
%test(example2) :-
%    holds(knows(bob,loc(c)),do(read(bob),s0)).
%test(example3) :-
%    holds(knows(bob,~?([L:location]:knows(ann,loc(L)))),s0).
%test(example4) :-
%    holds(~knows(bob,~?([L:location]:knows(ann,loc(L)))),do(leave(bob),s0)).

:- end_tests(domain).

