
agent(sam).
agent(max).

resource(box1).
resource(box2).

room(room1).
room(room2).

object(O) :- agent(O).
object(O) :- resource(O).

% Enumerates primitive actions, and the domains of their arguments.
prim_action(pickup(agent,resource)).
prim_action(drop(agent,resource)).
prim_action(move(agent,room)).

% Enumerates primitive fluents, and domains of arguments
prim_fluent(holding(agent,resource)).
prim_fluent(inroom(object, room)).

% Enumerates functional fluents, and domains of arguments
% none in this domain...

% Enumerates conditions for action description predicate fluents
adp_fluent(poss,pickup(_,Res),C) :-
    C = ~ (? ([A] : holding(A,Res))).
adp_fluent(poss,drop(Agt,Res),C) :-
    C = holding(Agt,Res).
adp_fluent(poss,move(_,_),true).

adp_fluent(canObs(Agt),pickup(Agt2,_),(?([R]:inroom(Agt,R) & inroom(Agt2,R)))).
adp_fluent(canObs(Agt),drop(Agt2,_),(?([R]:inroom(Agt,R) & inroom(Agt2,R)))).
adp_fluent(canObs(Agt),move(Agt2,Rm),(?([R]:inroom(Agt,R) & inroom(Agt2,R)) | inroom(Agt,Rm))).

% Enumerates the fluents holding in the initial situation
initially(inroom(sam,room1)).
initially(inroom(box1,room1)).
initially(inroom(max,room2)).
initially(inroom(box2,room2)).

% Causal rules for each fluent/action combo
causes_true(holding(Agt,Res),pickup(Agt2,Res2),(Agt=Agt2) & (Res=Res2)).
causes_false(holding(Agt,Res),drop(Agt2,Res2),(Agt=Agt2) & (Res=Res2)).

causes_true(inroom(Agt,Rm),move(Agt2,Rm2),(Agt=Agt2) & (Rm=Rm2)).
causes_false(inroom(Agt,Rm),move(Agt2,Rm2),(Agt=Agt2) & (Rm\=Rm2)).


% Specify domain constraints as additional background knowledge
%
constraint(!([Agt1,Agt2,Obj] : (~(holding(Agt1,Obj) & holding(Agt2,Obj)) | Agt1=Agt2))).

