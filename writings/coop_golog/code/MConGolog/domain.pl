
%%  List agents in the system
agent(agent1).
agent(agent2).
agent(agent3).

%%%%%  Axioms for resources   %%%%%

%%  List the resources in the system
resource(knife1).
resource(knife2).
resource(knife3).
resource(board1).
resource(board2).
resource(bowl1).
resource(bowl2).
resource(bowl3).
resource(oven).


%% Allow an agent to acquire a resource
prim_action(acquire_resource(Agt,Res)) :-
    agent(Agt), resource(Res).
%% Allow an agent to release a resource
prim_action(release_resource(Agt,Res)) :-
    agent(Agt), resource(Res).

%% Indicate the resources posessed by an agent
prim_fluent(has_resource(Agt,Res)) :-
    agent(Agt), resource(Res).

%% Preconditions require the resource to be available
poss(acquire_resource(_,Res),S) :-
    \+ has_resource(_,Res,S).
poss(release_resource(Agt,Res),S) :-
    has_resource(Agt,Res,S).

%% Successor State Axioms
has_resource(Agt,Res,do(C,S)) :-
    member(acquire_resource(Agt,Res),C) 
    ;
    has_resource(Agt,Res,S), \+ member(release_resource(Agt,Res),C).

%% Initially, no-one has any resources
has_resource(_,_,s0) :- fail.

%%%%  Simple Test Program  %%%%%%

testprog(D) :-
    D = conc(seq(acquire_resource(agent1,knife1),
                 conc(acquire_resource(agent2,knife2),
                      acquire_resource(agent3,knife3))),
             conc(acquire_resource(agent1,bowl1),
                  acquire_resource(agent2,bowl2)))
    .


