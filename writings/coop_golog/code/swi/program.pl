%%
%%  ConGolog procedures
%%
%%  The following are a collection of useful procedures in the domain,
%%  from which larger programs can be built.
%%


%%  Main control program - prepare a nice meal
%%
proc(makeDinner,
     makeSalad(thomas,bowl1) // makeCake(thomas,bowl2)
    ).

%%  Ensure that the agent has control of an object
%%
proc(ensureHas(Agt,Obj),
     if(has_object(Agt,Obj,now),nil,acquire_object(Agt,Obj))
    ).

%%  Carry out the necessary sequence of actions to place one object
%%  inside another, releasing the destination container when done.
%%
proc(doPlaceIn(Agt,Obj,Dest),
     ensureHas(Agt,Obj) // ensureHas(Agt,Dest)
     : place_in(Agt,Obj,Dest)
     : (nil / release_object(Agt,Dest))
    ).

%%  Nondeterministically select an object of a given type, gain control
%%  of it, and place it inside a container object.
%%
proc(doPlaceTypeIn(Agt,Type,Dest),
     pi(obj,?obj_is_type(obj,Type)
            : acquire_object(Agt,obj)
            : doPlaceIn(Agt,obj,Dest))
    ).

%%  Carry out the necessary actions to transfer the contents of one
%%  container to another, relasing both when finished.
%%
proc(doTransfer(Agt,Source,Dest),
     ensureHas(Agt,Source) // ensureHas(Agt,Dest)
     : transfer(Agt,Source,Dest)
     : (release_object(Agt,Source) / nil) // (release_object(Agt,Dest) / nil)
    ).

%%  Make a simple cake mixture in the specified container.
%%
proc(makeCakeMix(Agt,Dest),
     doPlaceTypeIn(Agt,egg,Dest)
     : doPlaceTypeIn(Agt,flour,Dest)
     : doPlaceTypeIn(Agt,sugar,Dest)
     : ensureHas(Agt,Dest)
     : mix(Agt,Dest)
     : release_object(Agt,Dest)
    ).

%%  Make a cake in the specified container.  This involves
%%  making cake mix in the container, then baking it in an oven.
%%
proc(makeCake(Agt,Dest),
     makeCakeMix(Agt,Dest)
     : pi(myOven, ?obj_is_type(myOven,oven)
                  : ensureHas(Agt,myOven)
                  : ensureHas(Agt,Dest)
                  : place_in(Agt,Dest,myOven)
                  : pi(myBoard, ?obj_is_type(myBoard,board)
                                : doTransfer(Agt,myOven,myBoard)
                      ))
    ).


%%  Chop the given item then place it in the given container.
%%  Releases control of the container when done.  An empty chopping
%%  board is selected nondeterministically.
%%
proc(doChopInto(Agt,Obj,Dest),
     ensureHas(Agt,Obj)
     : pi(myBoard, ?obj_is_type(myBoard,board)
     : pi(myKnife, ?obj_is_type(myKnife,knife)
                   : ?neg(contents(myBoard,_,now))
                   : ensureHas(Agt,myBoard)
                   : ensureHas(Agt,myKnife)
                   : place_in(Agt,Obj,myBoard)
                   : chop(Agt,myBoard)
                   : ensureHas(Agt,Dest)
                   : transfer(Agt,myBoard,Dest)
                   : release_object(Agt,myBoard) // release_object(Agt,Dest)
                     // release_object(Agt,myKnife)
         )
         )
    ).


%%  Make a salad in the specified container.  This involves selecting
%%  appropriate vegetables, chopping them, placing them in the container,
%%  and mixing briefly.
%%
proc(makeSalad(Agt,Dest),
       pi(obj, ?obj_is_type(obj,lettuce)
                      : acquire_object(Agt,obj)
                      : doChopInto(Agt,obj,Dest)
         )
       //
       pi(obj, ?obj_is_type(obj,tomato)
                      : acquire_object(Agt,obj)
                      : doChopInto(Agt,obj,Dest)
         )
      //
      pi(obj, ?obj_is_type(obj,carrot)
                      : acquire_object(Agt,obj)
                      : doChopInto(Agt,obj,Dest)
        )
      : ensureHas(Agt,Dest)
      : mix(Agt,Dest)
      : release_object(Agt,Dest)
    ).


