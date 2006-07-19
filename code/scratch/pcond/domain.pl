
agent(thomas).
agent(richard).
agent(harriet).

resource(knife1).
resource(knife2).
resource(knife3).
resource(board1).
resource(board2).
resource(bowl1).
resource(bowl2).
resource(bowl3).
resource(oven).


% Enumerates primitive actions
prim_action(pickup(Agt,Res)) :-
    agent(Agt), resource(Res).
prim_action(putdown(Agt,Res)) :-
    agent(Agt), resource(Res).
prim_action(drop(Agt,Res)) :-
    agent(Agt), resource(Res).

% Enumerates primitive fluents
prim_fluent(holding(Agt,Res)) :-
    agent(Agt), resource(Res).
prim_fluent(fragile(Res)) :-
    resource(Res).
prim_fluent(broken(Res)) :-
    resource(Res).

% Enumerates conditions for action description predicate fluents
adp_fluent(poss,pickup(_,Res),C) :-
    C = -exists(A,holding(A,Res)).
adp_fluent(poss,putdown(Agt,Res),C) :-
    C = holding(Agt,Res).
adp_fluent(poss,drop(Agt,Res),C) :-
    C = holding(Agt,Res).

adp_fluent(canObs(Agt),pickup(Agt2,_),(Agt=Agt2)).
adp_fluent(canObs(Agt),putdown(Agt2,_),(Agt=Agt2)).
adp_fluent(canObs(Agt),drop(Agt2,_),(Agt=Agt2)).

adp_fluent(legObs(Agt),A,C) :-
    adp_fluent(poss,A,C1),
    adp_fluent(canObs(Agt),A,C2),
    C = C1 & -C2.

% Enumerates the fluents holding in the initial situation
initially(_) :-
    fail.

% Causal rules for each fluent/action combo
causes_true(holding(Agt,Res),pickup(Agt,Res),true).
causes_false(holding(Agt,Res),putdown(Agt,Res),true).
causes_false(holding(Agt,Res),drop(Agt,Res),true).

causes_true(broken(Res),drop(_,Res2),(Res=Res2) & fragile(Res2)).


