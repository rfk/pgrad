%%
%%  domain.pl:  Axiomatisation of the "Cooking Agents" domain for MConGolog
%%
%%  Author:  Ryan Kelly (rfk)
%%
%%  Date Created:  28/07/05
%%
%%    This file contains an axiomatisation of the "Cooking Agents" domain
%%    in the Concurrent, Temporal Situation Calculus with Natural Actions.
%%
%%    The domain consists of several agents and inanimate objects of
%%    different types (indicated by prim_object/2) which in turn may
%%    be part of super-types (indicated by super_type/2).
%%
%%    Agents may acquire objects, place them inside/on container objects,
%%    and transfer the contents of one container object to another.  There
%%    are also an unlimited supply of timers in the world which may be
%%    set to ring at a specified time in the future.
%%
%%    The agents may also perform several continuous tasks, which have
%%    durations and may span several situations.  Agents may only perform
%%    one task at a time.
%%
%%    Depending on the tasks being performed, the contents of container
%%    objects may evolve from one situation to another.  For example,
%%    if the task mix(bowl1,5) is being performed (mix the contents of
%%    bowl1 for five minutees) then the contents might evolve from
%%    [egg1,flour1,sugar1] to mixed([egg1,flour1,sugar1],5).
%%


%%  
%%  agent(Agt):  specify agents in the system
%%
%%  This predicate is true when Agt is the name of an agent in the world.
%%
agent(thomas).
agent(richard).
%agent(harriet).


%% 
%%  task(T):  specify the tasks that can be performed
%%
%%  This predicate is true when T is a task that the agents in the system
%%  can perform.  Tasks are typically parameterised in terms of the
%%  objects on which they operate.
%%

%%  mix(Cont,Dur):  mix the contents of container Cont for duration Dur
task(mix(Cont,_)) :- 
    obj_is_type(Cont,container).

%%  chop(Cont):  chop the contents of container Cont
task(chop(Conatainer)) :-
    obj_is_type(Cont,container).

%%
%%  task_diration(Agt,Task,Dur):  specify duration of tasks
%%
%%  This predicate is true when Dur is the time taken by agent Agt
%%  to perform the task Task.
%%
task_duration(_,mix(_,D),D).
task_duration(Agt,chop(_),D) :-
    (Agt = richard ->
        D = 5
    ;
        D = 3
    ).


%%
%%  prim_obj(Obj,Type):  specify primitive objects in the world
%%
%%  This predicate is true when Obj is the name of a primitive object
%%  in the world, of type Type.
%%
%%  prim_obj(Obj):  shortcut to check object names
%%
%%  This predicate is true if Obj is the name of a primite object,
%%  regardless of its type.
%%

prim_obj(Obj) :-
    prim_obj(Obj,_).

prim_obj(Obj,knife) :-
    member(Obj,[knife1,knife2,knife3]).
prim_obj(Obj,bowl) :-
    member(Obj,[bowl1,bowl2]).
prim_obj(Obj,board) :-
    member(Obj,[board1,board2]).
prim_obj(Obj,oven) :-
    member(Obj,[oven1]).
prim_obj(Obj,flour) :-     % flour measured in 'units' for simplicity
    member(Obj,[flour1,flour2]).
prim_obj(Obj,sugar) :-     % same for the sugar
    member(Obj,[sugar1,sugar2]).
prim_obj(Obj,egg) :-
    member(Obj,[egg1,egg2,egg3]).
prim_obj(Obj,tomato) :-
    member(Obj,[tomato1,tomato2]).
prim_obj(Obj,lettuce) :-
    member(Obj,[lettuce1]).


%%
%%  super_type(SubType,SuperType):  specify type hierarchy
%%
%%  This predicate is true when all objects of type SubType are
%%  also of type SuperType.
%%  
super_type(Type,container) :-
    member(Type,[bowl,board,oven]).
super_type(Type,ingredient) :-
    member(Type,[flour,egg,tomato,lettuce,sugar]).

%%
%%  obj_is_type(Obj,Type):  check object types
%%
%%  This predicate is true when the object named Obj is of type
%%  Type according to the hierarchy of super-types.
%%
obj_is_type(Obj,Type) :-
    prim_obj(Obj,Type)
    ;
    super_type(SubType,Type), obj_is_type(Obj,SubType).


%%
%%  prim_action(Act):  specify primitive actions
%%
%%  This predicate is true when Act is the name of a primitive action
%%  in the world.  Actions are typically parameterised in terms of the
%%  objects they act on.  See the details of the MConGolog situation
%%  calculus for further information.
%%

%%  acquire_object(Agt,Obj):  agent acquires control of an object
prim_action(acquire_object(Agt,Obj)) :-
    agent(Agt), prim_obj(Obj).

%%  release_object(Agt,Obj):  agent releases an object it has acquired
prim_action(release_object(Agt,Obj)) :-
    agent(Agt), prim_obj(Obj).

%%  set_timer(Agt,ID,Dur):  agent sets timer with name ID to ring Dur
%%  minutes in the future
prim_action(set_timer(Agt,_,_)) :-
    agent(Agt).

%%  ring_timer(ID):  timer with name ID rings, a natural action
prim_action(ring_timer(_)).
natural(ring_timer(_)).

%%  place_in(Agt,Conts,Dest):  agent places object Conts in container Dest
prim_action(place_in(Agt,Conts,Dest)) :-
    agent(Agt), prim_obj(Conts), obj_is_type(Dest,container).

%%  transfer(Agt,Source,Dest):  agent transfers contents of container Source
%%  to container Dest
prim_action(transfer(Agt,Source,Dest)) :-
    agent(Agt), obj_is_type(Source,container),
    obj_is_type(Dest,container).

%%  begin_task(Agt,Task):  agent starts performing task Task
prim_action(begin_task(Agt,Task)) :-
    agent(Agt), task(Task).

%%  end_task(Agt,Task):  agent finishes performing task, a natural action
prim_action(end_task(Agt,Task)) :-
    agent(Agt), task(Task).
natural(end_task(_,_)).


%%
%%  poss(A,T,S):  possibility of performing an action
%%
%%  This predicate is true when it is possible to perform action
%%  A at time T in situation S.
%%

%%  Agents can only acquire an object if no agent already has it,
%%  they arent doing a task, and the object hasnt been used.
poss(acquire_object(Agt,Obj),_,S) :-
    \+ has_object(_,Obj,S), \+ doing_task(Agt,_,_,S), \+ used(Obj,S).

%%  Agents may only release objects that they have, when they arent
%%  currently performing a task
poss(release_object(Agt,Obj),_,S) :-
    has_object(Agt,Obj,S), \+ doing_task(Agt,_,_,S).

%%  Agents may set a timer as long as it hasnt already been set, and
%%  they arent currently performing a task
poss(set_timer(Agt,ID,_),_,S) :-
    \+ timer_set(ID,_,S), \+ doing_task(Agt,_,_,S).

%%  It is only possible for a timer to ring once its remaining time
%%  has precisely elapsed
poss(ring_timer(ID),T,S) :-
    timer_set(ID,Dur,S),
    start(S,SStart), T .=. SStart + Dur.

%%  Agents may place an object in a container provided they have possession
%%  of both, and arent currently doing a task
poss(place_in(Agt,Conts,Dest),_,S) :-
    has_object(Agt,Conts,S), has_object(Agt,Dest,S),
    \+ doing_task(Agt,_,_,S).

%%  Agents may transfer contents from one container to another as long
%%  as they have possession of both, and arent doing a task
poss(transfer(Agt,Source,Dest),_,S) :-
    has_object(Agt,Source,S), has_object(Agt,Dest,S),
    \+ doing_task(Agt,_,_,S).

%%  Agents may begin the mix() task as long as they arent doing another
%%  task, and have possession of the container to be mixed in
poss(begin_task(Agt,mix(Obj,_)),_,S) :-
    has_object(Agt,Obj,S), \+ doing_task(Agt,_,_,S).

%%  Agents may begin the chop() task as long as they arent doing another
%%  task, and have possession of the container whose contents to chop
poss(begin_task(Agt,chop(Obj)),_,S) :-
    has_object(Agt,Obj,S), \+ doing_task(Agt,_,_,S).

%%  Agents may end a task only when precisely the remaining amount of
%%  time has elapsed
poss(end_task(Agt,Task),T,S) :-
    doing_task(Agt,Task,Remain,S),
    start(S,SStart), T .=. SStart + Remain.


%%
%%  conflicts(C,T,S):  concurrent actions conflict
%%
%%  This predicate must be true when concurrent actions in C conflict
%%  and cannot be performed at time T in situation S.
%%

%%  Agents cannot do more than one action at a time
conflicts(C,_,_) :-
    member(A1,C), actor(A1,Agt),
    member(A2,C), actor(A2,Agt),
    A2 \= A1.

%%  Two agents cannot acquire the same object
conflicts(C,_,_) :-
    member(acquire_object(A1,Res),C),
    member(acquire_object(A2,Res),C),
    A1 \= A2.
    
%%
%%  Fluents in the Domain
%%
%%  The fluents are specified in terms of their successor state axioms,
%%  of the form "a fluent is true if it became true, or was previously
%%  true did not become false".
%%
%%    fluent_holds(Args,do(A,T,S)) :-
%%        fluent_becomes_true(Args,do(A,T,S))
%%        ;
%%        (
%%          fluent_holds(Args,S),
%%          \+ fluent_becomes_false(Args,do(A,T,S))
%%        )
%%

%%
%%  has_object(Agt,Obj,S):  agent has an object
%%
%%  This fluent is true when agent Agt has possession of the object Obj
%%  in situation S.  It can become true by acquiring the object, and
%%  false by releasing the object or if it has become used.
%%
has_object(Agt,Obj,do(C,T,S)) :-
    member(acquire_object(Agt,Obj),C)
    ;
    has_object(Agt,Obj,S),
    \+ (
       member(release_object(Agt,Obj),C)
       ;
       used(Obj,do(C,T,S))
    ).

%%
%%  used(Obj,S):  object is used in situation S
%%
%%  This fluent is true when an object has been used - for example,
%%  an ingredient has been placed in a container.  Once an object has
%%  been used, it cannot be used again.
%%
used(Obj,do(C,_,S)) :-
    prim_obj(Obj), obj_is_type(Obj,ingredient),
    (
      used(Obj,S)
      ;
      member(place_in(_,Obj,_),C)
    ).

%%
%%  timer_set(ID,Dur,S):  timer is set in situation S
%%
%%  This fluent indicates that the timer named ID is set to ring in Dur
%%  minutes in situation S.  It becomes true as a result of a set_timer()
%%  action, TODO more here.
%%
timer_set(ID,Dur,do(C,T,S)) :-
    member(set_timer(_,ID,Dur),C)
    ;
    timer_set(ID,OldDur,S), start(S,SStart), Dur .=. OldDur-(T-SStart),
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
             NewP .=. OldP+(T-SStart), Conts = mixed(MixConts,NewP)
         ;
             Conts = mixed(OldConts,0)
      )
      ;
      member(end_task(_,mix(Obj,_)),C), contents(Obj,mixed(MixConts,OldP),S),
      NewP .=. OldP+(T-SStart), Conts = mixed(MixConts,NewP)
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
    OldRem .=. Remain-(T-SStart), \+ member(end_task(Agt,Task),C).
    

history_length(N,do(_,_,S)) :-
    history_length(N1,S),
    N is N1 + 1.
history_length(0,s0).

%%  Intial Conditions
start(s0,0).


proc(ensureHas(Agt,Obj),
     if(has_object(Agt,Obj,now),nil,acquire_object(Agt,Obj))
    ).

proc(doPlaceIn(Agt,Obj,Dest),
     ensureHas(Agt,Obj) // ensureHas(Agt,Dest)
     : place_in(Agt,Obj,Dest)
     : release_object(Agt,Dest)
    ).

proc(doPlaceTypeIn(Agt,Type,Dest),
     pi(obj,?obj_is_type(obj,Type)
            : acquire_object(Agt,obj)
            : doPlaceIn(Agt,obj,Dest))
    ).

proc(doTransfer(Agt,Source,Dest),
     ensureHas(Agt,Source) // ensureHas(Agt,Dest)
     : transfer(Agt,Source,Dest)
     : release_object(Agt,Source) // release_object(Agt,Dest)
    ).

proc(makeCakeMix(Dest),
     pi(agt,?agent(agt) : doPlaceTypeIn(agt,egg,Dest))
     : pi(agt,?agent(agt) : doPlaceTypeIn(agt,flour,Dest))
     : pi(agt,?agent(agt) : doPlaceTypeIn(agt,sugar,Dest))
     : pi(agt, ?agent(agt) : acquire_object(agt,Dest)
                           : begin_task(agt,mix(Dest,5))
                           : end_task(agt,mix(Dest,5))
                           : release_object(agt,Dest))
    ).

proc(makeCake(Dest),
     makeCakeMix(Dest)
     : pi(myOven, ?obj_is_type(myOven,oven)
                  : pi(agt, doPlaceIn(agt,Dest,myOven)
                            : set_timer(agt,cakeTimer,35)
                      )
                  : ring_timer(cakeTimer)
                  : pi(agt,pi(myBoard, ?obj_is_type(myBoard,board)
                                       : doTransfer(agt,myOven,myBoard)
                      ))
         )
    ).


proc(control,
     makeCake(bowl1) // makeCake(bowl2)
    ).


%%  Tests the operation of the LNTP condition
proc(timerTest,
     set_timer(thomas,timer1,5)
     : set_timer(richard,timer2,7)
     : ring_timer(timer2)
    ).

%%  Tests the operation of concurrency with nondeterminism
%%  The test of history_length prunes solutions that dont make
%%  full use of the concurrency (there are LOTS!).
proc(concTest,
     doPlaceTypeIn(thomas,egg,bowl1) // doPlaceTypeIn(richard,egg,bowl2)
     : ?history_length(4,now)
    ).

proc(piTest,
     acquire_object(thomas,egg1)
     : pi(obj, ?and(obj_is_type(obj,egg),neg(has_object(_,obj,now)))
               : acquire_object(richard,board1)
               : acquire_object(richard,obj)
         )
    ).

