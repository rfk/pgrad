
%%  List agents in the system
agent(agent1).
agent(agent2).
agent(agent3).

senses(_,_) :-
    fail.

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

%% Causal laws of possession are very simple
causes_val(acquire_resource(Agt,Res),has_resource(Agt,Res),1,true).
causes_val(release_resource(Agt,Res),has_resource(Agt,Res),0,true).

%% Preconditions require the resource to be available
poss(acquire_resource(_,Res),neg(some(a,has_resource(a,Res)=1))).
poss(release_resource(Agt,Res),has_resource(Agt,Res)=1).

%% Initially, all resources are available
initially(has_resource(_,_),0).


%%%%  Simple Test Program  %%%%%%

proc(control,
     [acquire_resource(agent1,knife1),
      acquire_resource(agent2,knife2),
      release_resource(agent2,knife2),
      acquire_resource(agent3,knife2)
     ]).


execute(Action,History,SensingResult) :-
    write('Executing action: '), write(Action), nl,
    (senses(Action,_) ->
        (write('[Enter Sensing value, terminate with "."]: '),
            read(SensingResult))
        ;
        nl).


exog_occurs(ExogList) :-
    ExogList = [].


initialize.
finalize.

