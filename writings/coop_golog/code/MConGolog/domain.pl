

%% List the agents in the system
agent(thomas).
agent(richard).
agent(harriet).


%% List the tasks that can be done
task(mix(Container,Duration)).
task(chop(Conatainer)).

task_duration(_,mix(_,D),D).
task_duration(Agt,chop(_),D) :-
    (Agt = richard ->
        D = 5
    ;
        D = 3
    ).


%% List the primitive objects and their types.
%% prim_obj(Obj,Type) is rue when Obj is an object of type
%% Type.  This can be used to implement subtypes.
prim_obj(Obj,knife) :-
    member(Obj,[knife1,knife2,knife3]).
prim_obj(Obj,bowl) :-
    member(Obj,[bowl1,bowl2]).
prim_obj(Obj,board) :-
    member(Obj,[board1,board2]).
prim_obj(Obj,oven) :-
    member(Obj,[oven1]).
prim_obj(Obj,flour) :-  % flour measured in 'units' for simplicity
    member(Obj,[flour1,flour2,flour3,flour4,flour5,flour6,flour7]).
prim_obj(Obj,egg) :-
    member(Obj,[egg1,egg2,egg3]).
prim_object(Obj,tomato) :-
    member(Obj,[tomato1,tomato2]).
prim_object(Obj,lettuce) :-
    member(Obj,[lettuce1]).
prim_object(Obj,sugar) :-
    member(Obj,[sugar1,sugar2,sugar3,sugar4,sugar5]).

prim_obj(Obj,container) :-
    prim_obj(Obj,bowl) ; prim_obj(Obj,board) ;
    prim_obj(Obj,oven).

prim_obj(Obj,ingredient) :-
    prim_obj(Obj,flour) ; prim_obj(Obj,egg) ;
    prim_obj(Obj,tomato) ; prim_obj(Obj,lettuce) ;
    prim_obj(Obj,sugar).


%%  Primitive Actions

prim_action(aquire_object(Agt,Obj)) :-
    agent(Agt), prim_obj(Obj).
prim_action(release_object(Agt,Obj)) :-
    agent(Agt), prim_obj(Obj).
prim_action(set_timer(Agt,ID,Duration)) :-
    agent(Agt).
prim_action(ring_timer(ID)).
natural(ring_timer(_)).

prim_action(place_in(Agt,Conts,Dest)) :-
    agent(Agt), prim_obj(Dest).
prim_action(transfer(Agt,Source,Dest)) :-
    agent(Agt), prim_obj(Source), prim_obj(Dest).
prim_action(begin_task(Agt,Task)) :-
    agent(Agt), task(Task).
prim_action(end_task(Agt,Task)) :-
    agent(Agt), task(Task).
natural(end_task(_,_)).


%%  Possibility Axioms - fake it for time being
poss(_,_,_).


%%  Fluents in the domain

has_object(Agt,Res,do(C,_,S)) :-
    member(aquire_object(Agt,Res),C)
    ;
    has_object(Agt,Res,S), \+ member(release_object(Agt,Res),C).

timer_set(ID,Dur,do(C,T,S)) :-
    member(set_timer(_,ID,Dur),C)
    ;
    timer_set(ID,OldDur,S), start(S,SStart), Dur $= OldDur-(T-SStart),
    \+ member(ring_timer(ID),C).

contents(Obj,Conts,do(C,T,S)) :-
    start(S,SStart),
    ((
      %% All the ways it can become true
      (member(place_in(_,Conts,Obj),C)
         ; member(transfer(_,Obj2,Obj),C), contents(Obj2,Conts,S)),
      \+ contents(Obj,_,S)
      ;
      (member(place_in(_,NewConts,Obj),C)
         ; member(transfer(_,Obj2,Obj),C), contents(Obj2,NewConts,S)),
      contents(Obj,OldConts,S),
      ( OldConts = [_|_] -> OldContsL = OldConts ; OldContsL = [OldConts]),
      ( NewConts = [_|_] -> NewContsL = NewConts ; NewContsL = [NewConts]),
      union(OldContsL,NewContsL,Conts)
      ;
      doing_task(_,mix(Obj,_),_,do(C,T,S)), contents(Obj,OldConts,S),
      (  OldConts = mixed(MixConts,OldP) ->
             NewP $= OldP+(T-SStart), Conts = mixed(MixConts,NewP)
         ;
             Conts = mixed(OldConts,0)
      )
      ;
      member(end_task(_,mix(Obj,_)),C), contents(Obj,mixed(MixConts,OldP),S),
      NewP $= OldP+(T-SStart), Conts = mixed(MixConts,NewP)
      ;
      member(end_task(_,chop(Obj)),C), contents(Obj,OldConts,S),
      Conts = chopped(OldConts)
    )
    ;
    %% Or it was true, and didnt become false...
    contents(Obj,Conts,S), \+ (
        %% All the ways it can become false
        member(transfer(_,Obj,_),C)
        ;
        member(transfer(_,Obj2,Obj),C), contents(Obj2,_,S)
        ;
        member(place_in(_,_,Obj),C)
        ;
        doing_task(_,mix(Obj,_),_,do(C,T,S))
        ;
        member(end_task(_,mix(Obj,_)),C)
        ;
        member(end_task(_,chop(Obj)),C)
    )).


doing_task(Agt,Task,Remain,do(C,T,S)) :-
    member(begin_task(Agt,Task),C), task_duration(Agt,Task,Remain)
    ;
    doing_task(Agt,Task,OldRem,S), start(S,SStart),
    OldRem $= Remain-(T-SStart), \+ member(end_task(Agt,Task),C).
    

start(s0,0).


testsit(S) :-
    S1 = do([place_in(thomas,egg1,bowl1)],_,s0),
    S2 = do([place_in(harriet,flour1,bowl1)],_,S1),
    S3 = do([begin_task(richard,mix(bowl1,5))],T,S2), T2 $= T + 5,
    S4 = do([end_task(richard,mix(bowl1,5))],T2,S3),
    S = S4.
