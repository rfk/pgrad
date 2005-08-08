

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
%% prim_obj(Obj,Type) is true when Obj is an object of type
%% Type.
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
prim_obj(Obj,flour) :-  % flour measured in 'units' for simplicity
    member(Obj,[flour1,flour2,flour3,flour4,flour5,flour6,flour7]).
prim_obj(Obj,egg) :-
    member(Obj,[egg1,egg2,egg3]).
prim_obj(Obj,tomato) :-
    member(Obj,[tomato1,tomato2]).
prim_obj(Obj,lettuce) :-
    member(Obj,[lettuce1]).
prim_obj(Obj,sugar) :-
    member(Obj,[sugar1,sugar2,sugar3,sugar4,sugar5]).


%%  List object super-types using super_type(subtype,supertype)

super_type(Type,container) :-
    member(Type,[bowl,board,oven]).
super_type(Type,ingredient) :-
    member(Type,[flour,egg,tomato,lettuce,sugar]).

obj_is_type(Obj,Type) :-
    prim_obj(Obj,Type)
    ;
    super_type(SubType,Type), obj_is_type(Obj,SubType).


%%  Primitive Actions

prim_action(acquire_object(Agt,Obj)) :-
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


%%  Possibility Axioms
poss(acquire_object(Agt,Obj),_,S) :-
    \+ has_object(_,Obj,S), \+ doing_task(Agt,_,_,S), \+ used(Obj,S).
poss(release_object(Agt,Obj),_,S) :-
    has_object(Agt,Obj,S), \+ doing_task(Agt,_,_,S).
poss(set_timer(Agt,ID,_),_,S) :-
    \+ timer_set(ID,_,S), \+ doing_task(Agt,_,_,S).
poss(ring_timer(ID),T,S) :-
    timer_set(ID,Dur,S),
    start(S,SStart), T $= SStart + Dur.
poss(place_in(Agt,Conts,Dest),_,S) :-
    has_object(Agt,Conts,S), has_object(Agt,Dest,S),
    prim_obj(Conts), obj_is_type(Dest,container),
    \+ doing_task(Agt,_,_,S).
poss(transfer(Agt,Source,Dest),_,S) :-
    has_object(Agt,Source,S), has_object(Agt,Dest,S),
    obj_is_type(Source,container), obj_is_type(Dest,container),
    \+ doing_task(Agt,_,_,S).
poss(begin_task(Agt,mix(Obj,_)),_,S) :-
    has_object(Agt,Obj,S), \+ doing_task(Agt,_,_,S).
poss(begin_task(Agt,chop(Obj)),_,S) :-
    has_object(Agt,Obj,S), \+ doing_task(Agt,_,_,S).
poss(end_task(Agt,Task),T,S) :-
    doing_task(Agt,Task,Remain,S),
    start(S,SStart), T $= SStart + Remain.


%%  Action conflict axioms
conflicts(C,_,_) :-
    member(A1,C), actor(A1,Agt),
    member(A2,C), actor(A2,Agt),
    A2 \= A1.
conflicts(C,_,_) :-
    member(acquire_object(A1,Res),C),
    member(acquire_object(A2,Res),C),
    A1 \= A2.
    
%%  Fluents in the domain

has_object(Agt,Obj,do(C,T,S)) :-
    member(acquire_object(Agt,Obj),C)
    ;
    has_object(Agt,Obj,S),
    \+ (
       member(release_object(Agt,Obj),C)
       ;
       used(Obj,do(C,T,S))
    ).

used(Obj,do(C,_,S)) :-
    prim_obj(Obj), obj_is_type(Obj,ingredient),
    (
      used(Obj,S)
      ;
      member(place_in(_,Obj,_),C)
    ).

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



proc(doPlaceIn(Agt,Obj,Dest),
     acquire_object(Agt,Obj) // acquire_object(Agt,Dest)
     : place_in(Agt,Obj,Dest)
     : release_object(Agt,Dest)
    ).

proc(doPlaceTypeIn(Agt,Type,Dest),
     pi(obj,?obj_is_type(obj,Type) : doPlaceIn(Agt,obj,Dest))
    ).

proc(makeCakeMix(Dest),
     doPlaceTypeIn(thomas,egg,Dest)
     : doPlaceTypeIn(thomas,flour,Dest) 
     : doPlaceTypeIn(thomas,sugar,Dest) 
     : acquire_object(thomas,Dest)
     : begin_task(thomas,mix(Dest,5)) : end_task(thomas,mix(Dest,5))
    ).

proc(control,
     acquire_object(thomas,bowl1)
     : begin_task(thomas,mix(bowl1,5)) : end_task(thomas,mix(bowl1,5))
    ).



testlens(Len1,Len2,Len3,LenP,LenT) :-
    bagof(S,do(doPlaceTypeIn(thomas,egg,bowl1),s0,S),L1),
    length(L1,Len1),
    bagof(S,do(doPlaceTypeIn(thomas,flour,bowl1),s0,S),L2),
    length(L2,Len2),
    bagof(S,do(doPlaceTypeIn(thomas,sugar,bowl1),s0,S),L3),
    length(L3,Len3),
    LenP is Len1 * Len2 * Len3,
    bagof(S,do(makeCakeMix(bowl1),s0,S),LT),
    length(LT,LenT).
