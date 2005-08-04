
%%  List agents in the system
agent(agent1).
agent(agent2).
agent(agent3).

%%%%%  Axioms for resources   %%%%%

%%  List the resources in the system, and their types
resource(knife1).
resource(knife2).
resource(knife3).
resource(board1).
resource(board2).
resource(bowl1).
resource(bowl2).
resource(bowl3).
resource(oven1).

res_type(knife1,knife).
res_type(knife2,knife).
res_type(knife3,knife).
res_type(board1,board).
res_type(board2,board).
res_type(bowl1,bowl).
res_type(bowl2,bowl).
res_type(bowl3,bowl).
res_type(oven1,oven).

%%  List the tasks, and their durations.
task(chop).
task(mix).


prim_action(acquire_resource(Agt,Res)) :-
    agent(Agt), resource(Res).

prim_action(release_resource(Agt,Res)) :-
    agent(Agt), resource(Res).

prim_action(set_timer(Agt,_,_)) :-
    agent(Agt).

prim_action(ring_timer(_)).
natural(ring_timer(_)).

prim_action(begin_task(Agt,Task,_)) :-
    agent(Agt), task(Task).

prim_action(end_task(Agt,Task,_)) :-
    agent(Agt), task(Task).
natural(end_task(_,_,_)).

prim_action(place_in(Agt,_,_)) :-
    agent(Agt).

prim_action(move_contents(Agt,_,_)) :-
    agent(Agt).




%% Indicate the resources posessed by an agent
prim_fluent(has_resource(Agt,Res)) :-
    agent(Agt), resource(Res).
%% Indicate the status of a timer: timer_set(ID,Duration)
prim_fluent(timer_set(_,_)).

%% Preconditions require the resource to be available
poss(acquire_resource(_,Res),_,S) :-
    \+ has_resource(_,Res,S).
poss(release_resource(Agt,Res),_,S) :-
    has_resource(Agt,Res,S).
%% Timers can only be set when not, must ring at specified time
poss(set_timer(_,ID,_),_,S) :-
    \+ timer_set(ID,_,S).
poss(ring_timer(ID),T,S) :-
    timer_set(ID,Duration,S),
    start(S,Sstart), T $= Sstart + Duration.

%% Agents can only do one thing at a time
conflicts(C,_,_) :-
    member(A1,C), actor(A1,Agt),
    member(A2,C), actor(A2,Agt),
    A2 \= A1.

%% Two agents cant acquire the same resource
conflicts(C,_,_) :-
    member(acquire_resource(A1,Res),C),
    member(acquire_resource(A2,Res),C),
    A1 \= A2.

%% Successor State Axioms
has_resource(Agt,Res,do(C,_,S)) :-
    member(acquire_resource(Agt,Res),C) 
    ;
    has_resource(Agt,Res,S), \+ member(release_resource(Agt,Res),C).

timer_set(ID,Dur,do(C,T,S)) :-
    member(set_timer(_,ID,Dur),C)
    ;
    timer_set(ID,OldDur,S), \+ member(ring_timer(ID),C),
    start(S,SStart), Dur is OldDur-(T-SStart).

%% Initially, no-one has any resources
has_resource(_,_,s0) :- fail.
%% No timers are set
timer_set(_,_,s0) :- fail.

start(s0,0).

%%%%  Simple Test Program  %%%%%%

testprog(D) :-
    D = conc(seq(acquire_resource(agent1,knife1),
                 conc(acquire_resource(agent2,knife2),
                      acquire_resource(agent3,knife3))),
             conc(acquire_resource(agent1,bowl1),
                  seq(set_timer(agent2,timer1,5),
		      seq(ring_timer(timer1),
		          acquire_resource(agent2,bowl2)))))
    .

testprog2(D) :-
    D = seq(set_timer(agent1,timer1,5),ring_timer(timer1))
    .


