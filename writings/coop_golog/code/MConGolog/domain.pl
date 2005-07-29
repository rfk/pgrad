
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
prim_action(acquire_resource(Agt,Res,_)) :-
    agent(Agt), resource(Res).
%% Allow an agent to release a resource
prim_action(release_resource(Agt,Res,_)) :-
    agent(Agt), resource(Res).

%% Indicate the resources posessed by an agent
prim_fluent(has_resource(Agt,Res)) :-
    agent(Agt), resource(Res).

%% Preconditions require the resource to be available
poss(acquire_resource(_,Res,_),S) :-
    \+ has_resource(_,Res,S).
poss(release_resource(Agt,Res,_),S) :-
    has_resource(Agt,Res,S).

%% Agents can only do one thing at a time
conflicts(C,_) :-
    member(A1,C), actor(A1,Agt),
    member(A2,C), actor(A2,Agt),
    A2 \= A1.

%% Two agents cant acquire the same resource
conflicts(C,_) :-
    member(acquire_resource(A1,Res),C),
    member(acquire_resource(A2,Res),C),
    A1 \= A2.

%% Successor State Axioms
has_resource(Agt,Res,do(C,S)) :-
    member(acquire_resource(Agt,Res),C) 
    ;
    has_resource(Agt,Res,S), \+ member(release_resource(Agt,Res),C).

%% Initially, no-one has any resources
has_resource(_,_,s0) :- fail.

start(s0,0).

%%%%  Simple Test Program  %%%%%%

testprog(D) :-
    D = conc(seq(acquire_resource(agent1,knife1,T1),
                 conc(acquire_resource(agent2,knife2,T2),
                      acquire_resource(agent3,knife3,T3))),
             conc(acquire_resource(agent1,bowl1,T4),
                  acquire_resource(agent2,bowl2,T5)))
    .


