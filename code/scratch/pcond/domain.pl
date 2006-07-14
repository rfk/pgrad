
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
prim_action(acquire(Agt,Res)) :-
    agent(Agt), resource(Res).
prim_action(release(Agt,Res)) :-
    agent(Agt), resource(Res).

% Enumerates primitive fluents
prim_fluent(has_resource(Agt,Res)) :-
    agent(Agt), resource(Res).

% Enumerates conditions for action description predicate fluents
adp_fluent(poss,acquire(_,Res),C) :-
    C = -exists(xA,has_resource(xA,Res)).
adp_fluent(poss,release(Agt,Res),C) :-
    C = has_resource(Agt,Res).

% Enumerates the fluents holding in the initial situation
initially(_) :-
    fail.

% Causal rules for each fluent/action combo
causes_true(has_resource(Agt,Res),acquire(Agt,Res),true).
causes_false(has_resource(Agt,Res),release(Agt,Res),true).

