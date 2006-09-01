
:- discontiguous(causes_true/3).
:- discontiguous(causes_false/3).

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


% Enumerates primitive actions, and the domains of their arguments.
prim_action(pickup(agent,resource)).
prim_action(putdown(agent,resource)).
prim_action(drop(agent,resource)).

% Enumerates primitive fluents, and domains of arguments
prim_fluent(holding(agent,resource)).
prim_fluent(fragile(resource)).
prim_fluent(broken(resource)).

% Enumerates conditions for action description predicate fluents
adp_fluent(poss,pickup(_,Res),C) :-
    C = -exists([A:agent],holding(A,Res)).
adp_fluent(poss,putdown(Agt,Res),C) :-
    C = holding(Agt,Res).
adp_fluent(poss,drop(Agt,Res),C) :-
    C = holding(Agt,Res).

adp_fluent(canObs(Agt),pickup(Agt2,_),(Agt=Agt2)).
adp_fluent(canObs(Agt),putdown(Agt2,_),(Agt=Agt2)).
adp_fluent(canObs(Agt),drop(Agt2,_),(Agt=Agt2)).

% Enumerates the fluents holding in the initial situation
initially(_) :-
    fail.

% Causal rules for each fluent/action combo
causes_true(holding(Agt,Res),pickup(Agt2,Res2),(Agt=Agt2) & (Res=Res2)).
causes_false(holding(Agt,Res),putdown(Agt2,Res2),(Agt=Agt2) & (Res=Res2)).
causes_false(holding(Agt,Res),drop(Agt2,Res2),(Agt=Agt2) & (Res=Res2)).

causes_true(broken(Res),drop(_,Res2),(Res=Res2) & fragile(Res2)).


% Specify domain constraints as additional background knowledge
%
constraint(all([Agt1:agent,Agt2:agent,Obj:resource],-(holding(Agt1,Obj) & holding(Agt2,Obj)) | Agt1=Agt2)).



