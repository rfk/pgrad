
agent(ann).
agent(bob).

place(c).
place(d).

% Enumerates primitive actions, and the domains of their arguments.
prim_action(read(agent)).
prim_action(leave(agent)).
prim_action(enter(agent)).

% Enumerates primitive fluents, and domains of arguments
prim_fluent(loc(place)).
prim_fluent(inroom(agent)).

% Enumerates conditions for action description predicate fluents
adp_fluent(poss,read(Agt),inroom(Agt)).
adp_fluent(poss,enter(Agt),~ inroom(Agt)).
adp_fluent(poss,leave(Agt),inroom(Agt)).

adp_fluent(canObs(Agt),read(_),inroom(Agt)).
adp_fluent(canObs(Agt),leave(_),true).
adp_fluent(canObs(Agt),enter(_),true).

adp_fluent(sr(R),read(_),loc(R)).
adp_fluent(sr(ok),leave(_),true).
adp_fluent(sr(ok),enter(_),true).

% Enumerates the fluents holding in the initial situation
initially(inroom(ann)).
initially(inroom(bob)).

% Causal rules for each fluent/action combo
causes_true(inroom(Agt),enter(Agt2),(Agt=Agt2)).
causes_false(inroom(Agt),leave(Agt2),(Agt=Agt2)).

