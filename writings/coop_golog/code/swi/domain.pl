%%
%%  domain.pl:  Axiomatisation of the "Cooking Agents" domain for ConGolog
%%
%%  Author:  Ryan Kelly (rfk)
%%
%%  Date Created:  12/03/07
%%
%%    This file contains an axiomatisation of the "Cooking Agents" domain
%%    in the situation calculus.
%%
%%    The domain consists of several agents and inanimate objects of
%%    different types (indicated by prim_object/2) which in turn may
%%    be part of super-types (indicated by super_type/2).
%%


%%  
%%  agent(Agt):  specify agents in the system
%%
%%  This predicate is true when Agt is the name of an agent in the world.
%%
agent(thomas).
agent(richard).
agent(harriet).


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
    member(Obj,[flour1,flour2,flour3,flour4,flour5]).
prim_obj(Obj,sugar) :-     % same for the sugar
    member(Obj,[sugar1,sugar2,sugar3,sugar4,sugar5,sugar6]).
prim_obj(Obj,egg) :-
    member(Obj,[egg1,egg2,egg3]).
prim_obj(Obj,tomato) :-
    member(Obj,[tomato1,tomato2]).
prim_obj(Obj,lettuce) :-
    member(Obj,[lettuce1]).
prim_obj(Obj,carrot) :-
    member(Obj,[carrot1,carrot2,carrot3]).


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
%%  objects they act on.  See the details of the MIndiGolog situation
%%  calculus for further information.
%%

%%  acquire_object(Agt,Obj):  agent acquires control of an object
prim_action(acquire_object(Agt,Obj)) :-
    agent(Agt), prim_obj(Obj).

%%  release_object(Agt,Obj):  agent releases an object it has acquired
prim_action(release_object(Agt,Obj)) :-
    agent(Agt), prim_obj(Obj).

%%  place_in(Agt,Conts,Dest):  agent places object Conts in container Dest
prim_action(place_in(Agt,Conts,Dest)) :-
    agent(Agt), prim_obj(Conts), obj_is_type(Dest,container).

%%  transfer(Agt,Source,Dest):  agent transfers contents of container Source
%%  to container Dest
prim_action(transfer(Agt,Source,Dest)) :-
    agent(Agt), obj_is_type(Source,container),
    obj_is_type(Dest,container).


%%
%%  poss(A,S):  possibility of performing an action
%%
%%  This predicate is true when it is possible to perform action
%%  A in situation S.
%%

%%  Agents can only acquire an object if no agent already has it,
%%  and the object hasnt been used.
poss(acquire_object(_,Obj),S) :-
    \+ has_object(_,Obj,S), \+ used(Obj,S).

%%  Agents may only release objects that they have.
poss(release_object(Agt,Obj),S) :-
    has_object(Agt,Obj,S).

%%  Agents may place an object in a container provided they have possession
%%  of both.
poss(place_in(Agt,Conts,Dest),S) :-
    has_object(Agt,Conts,S), has_object(Agt,Dest,S).

%%  Agents may transfer contents from one container to another as long
%%  as they have possession of both.
poss(transfer(Agt,Source,Dest),S) :-
    has_object(Agt,Source,S), has_object(Agt,Dest,S).

%%  Agents may mix the contains of a container they have possession of.
poss(mix(Agt,Cont),S) :-
    has_object(Agt,Cont,S).

%%  Agents may chop the contents of a contanier they have in their
%%  posession, as long as they have a knife.
poss(chop(Agt,Obj),S) :-
    has_object(Agt,Obj,S), obj_is_type(K,knife), has_object(Agt,K,S).

%%
%%  Fluents in the Domain
%%
%%  The fluents are specified in terms of their successor state axioms,
%%  of the form "a fluent is true if it became true, or was previously
%%  true did not become false".
%%
%%    fluent_holds(Args,do(A,S)) :-
%%        fluent_becomes_true(Args,do(A,S))
%%        ;
%%        (
%%          fluent_holds(Args,S),
%%          \+ fluent_becomes_false(Args,do(A,S))
%%        )
%%

%%
%%  has_object(Agt,Obj,S):  agent has an object
%%
%%  This fluent is true when agent Agt has possession of the object Obj
%%  in situation S.  It can become true by acquiring the object, and
%%  false by releasing the object or if it has become used.
%%
has_object(Agt,Obj,do(A,S)) :-
    A = acquire_object(Agt,Obj)
    ;
    has_object(Agt,Obj,S),
    \+ (
       A = release_object(Agt,Obj)
       ;
       used(Obj,do(A,S))
    ).

%%
%%  used(Obj,S):  object is used in situation S
%%
%%  This fluent is true when an object has been used - for example,
%%  an ingredient has been placed in a container.  Once an object has
%%  been used, it cannot be used again.
%%
used(Obj,do(A,S)) :-
    prim_obj(Obj), obj_is_type(Obj,ingredient),
    (
      used(Obj,S)
      ;
      A  = place_in(_,Obj,_)
    ).


%%
%%  contents(Obj,Conts,S):  object contents in a situation
%%
%%  This fluent indicates that object Obj contains the contents Conts
%%  in situation S.  It can become true, become false, and change value
%%  in a variety of ways, each of which is documented with its
%%  implementation.
%%
contents(Obj,Conts,do(A,S)) :-
    ((
      %% --- All the ways it can become true
      %% It was previously empty, and contents were placed or transfered in
      (A = place_in(_,Conts,Obj)
         ; A = transfer(_,Obj2,Obj), contents(Obj2,Conts,S)),
      \+ contents(Obj,_,S)
      ;
      %% It previously had contents, and more contents were placed or
      %% transfered in.  Contents is then a list.
      (A = place_in(_,NewConts,Obj)
         ; A = transfer(_,Obj2,Obj), contents(Obj2,NewConts,S)),
      contents(Obj,OldConts,S),
      ( OldConts = [_|_] -> OldContsL = OldConts ; OldContsL = [OldConts]),
      ( NewConts = [_|_] -> NewContsL = NewConts ; NewContsL = [NewConts]),
      union(OldContsL,NewContsL,Conts)
      ;
      %% An agent mixed the contents.  If they were previously
      %% unmixed, they are encased in a mixed(conts) indicator.
      A = mix(_,Obj,_), contents(Obj,OldConts,S),
      (  OldConts = mixed(MixConts) ->
             Conts = mixed(MixConts)
         ;
             Conts = mixed(OldConts)
      )
      ;
      %% An agent chopped the contents.
      A = chop(_,Obj), contents(Obj,OldConts,S),
      Conts = chopped(OldConts)
      ;
      %% If the container is in an oven, its contents are baking.
      %% If they are not encapsulated in a baking() indicator then do so.
      \+ obj_is_type(Obj,oven), obj_is_type(Oven,oven),
      contents(Oven,Obj,do(A,S)), contents(Obj,OldConts,S),
      (  OldConts = baking(BakedConts) ->
             Conts = baking(BakedConts)
         ;
             Conts = baking(OldConts)
      )
      ;
      %% If the container was taken out of the oven, update to baked()
      \+ obj_is_type(Obj,oven), obj_is_type(Oven,oven),
      contents(Oven,Obj,S), A = transfer(_,Oven,_),
      contents(Obj,baking(BakedConts),S),
      Conts = baked(BakedConts)
    )
    ;
    %% Or it was true, and didnt become false...
    contents(Obj,Conts,S), \+ (
        %% --- All the ways it can become false
        %% The contents were transfered out
        A = transfer(_,Obj,_)
        ;
        %% New contents were transfered in
        A = transfer(_,Obj2,Obj), contents(Obj2,_,S)
        ;
        %% New contents were placed in
        A = place_in(_,_,Obj)
        ;
        %% The contents were mixed
        A = mix(_,Obj,_)
        ;
        %% The contents were chopped
        A = chop(_,Obj)
        ;
        %% The object is in an oven, hence will change
        \+ obj_is_type(Obj,oven), obj_is_type(Oven,oven),
        contents(Oven,Obj,do(A,S))
        ;
        %% The object was just taken out of an oven, hence will change
        \+ obj_is_type(Obj,oven), obj_is_type(Oven,oven),
        contents(Oven,Obj,S), A = transfer(_,Oven,_)
    )).


%%
%%  history_length(N,S):  length of the action histoy in a situation
%%
%%  This simple fluent encodes in N the number of actions that have
%%  taken place in the history of situation S.  It is used to make this
%%  information easily available to agents.
%%
history_length(N,do(_,S)) :-
    history_length(N1,S),
    N is N1 + 1.
history_length(0,s0).

%%
%%  Intial Conditions for the domain
%%
%%  The initial conditions are specified by additional clauses for
%%  each fluent, with the situation term set to the atom s0.  For
%%  the most part no fluents hold in the initial situation, so 
%%  there arent many clauses here.
%%

% initially, nothing is true...


%%
%%  MIndiGolog procedures
%%
%%  The following are a collection of useful procedures in the domain,
%%  from which larger programs can be built.
%%


%%  Ensure that the agent has control of an object
proc(ensureHas(Agt,Obj),
     if(has_object(Agt,Obj,now),nil,acquire_object(Agt,Obj))
    ).

%%  Carry out the necessary sequence of actions to place one object
%%  inside another, releasing the destination container when done.
proc(doPlaceIn(Agt,Obj,Dest),
     ensureHas(Agt,Obj) // ensureHas(Agt,Dest)
     : place_in(Agt,Obj,Dest)
     : (release_object(Agt,Dest) / nil)
    ).

%%  Nondeterministically select an object of a given type, gain control
%%  of it, and place it inside a container object.
proc(doPlaceTypeIn(Agt,Type,Dest),
     pi(obj,?obj_is_type(obj,Type)
            : acquire_object(Agt,obj)
            : doPlaceIn(Agt,obj,Dest))
    ).

%%  Carry out the necessary actions to transfer the contents of one
%%  container to another, relasing both when finished.
proc(doTransfer(Agt,Source,Dest),
     ensureHas(Agt,Source) // ensureHas(Agt,Dest)
     : transfer(Agt,Source,Dest)
     : release_object(Agt,Source) // release_object(Agt,Dest)
    ).

%%  Make a simple cake mixture in the specified container.
%%  The agents to perform the various steps are selected
%%  nondeterministically.
proc(makeCakeMix(Dest),
     pi(agt,?agent(agt) : doPlaceTypeIn(agt,egg,Dest))
     : pi(agt,?agent(agt) : doPlaceTypeIn(agt,flour,Dest))
     : pi(agt,?agent(agt) : doPlaceTypeIn(agt,sugar,Dest))
     : pi(agt, ?agent(agt) : acquire_object(agt,Dest)
                           : mix(agt,Dest)
                           : release_object(agt,Dest))
    ).

%%  Make a cake in the specified container.  This involves
%%  making cake mix in the container, then baking it in an oven.
proc(makeCake(Dest),
     makeCakeMix(Dest)
     : pi(myOven, ?obj_is_type(myOven,oven)
                  : pi(agt, ensureHas(agt,myOven)
                            : ensureHas(agt,Dest)
                            : place_in(agt,Dest,myOven)
                      )
                  : pi(agt,pi(myBoard, ?obj_is_type(myBoard,board)
                                       : doTransfer(agt,myOven,myBoard)
                      ))
         )
    ).


%%  Chop the given item then place it in the given container.
%%  Releases control of the container when done.  An empty chopping
%%  board is selected nondeterministically.
proc(doChopInto(Agt,Obj,Dest),
     ensureHas(Agt,Obj)
     : pi(myBoard, ?obj_is_type(myBoard,board)
                   : ?neg(contents(myBoard,_,now))
                   : ensureHas(Agt,myBoard)
                   : place_in(Agt,Obj,myBoard)
                   : chop(Agt,myBoard)
                   : ensureHas(Agt,Dest)
                   : transfer(Agt,myBoard,Dest)
                   : release_object(Agt,myBoard) // release_object(Agt,Dest)
         )
    ).


%%  Make a salad in the specified container.  This involves selecting
%%  appropriate vegetables, chopping them, placing them in the container,
%%  and mixing briefly.
proc(makeSalad(Dest),
       pi(agt,pi(obj, ?obj_is_type(obj,lettuce)
                      : acquire_object(agt,obj)
                      : doChopInto(agt,obj,Dest)
                )
         )
       //
       pi(agt,pi(obj, ?obj_is_type(obj,tomato)
                      : acquire_object(agt,obj)
                      : doChopInto(agt,obj,Dest)
                )
         )
      //
      pi(agt,pi(obj, ?obj_is_type(obj,carrot)
                      : acquire_object(agt,obj)
                      : doChopInto(agt,obj,Dest)
                )
        )
    : pi(agt, ensureHas(agt,Dest)
              : mix(agt,Dest)
              : release_object(agt,Dest)
        )
    ).


%%  Main control program - prepare a nice meal
proc(control,
     makeSalad(bowl1) // makeCake(bowl2)
     : ?(and(history_length(L,now),L<30))
    ).

