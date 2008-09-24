
functor 
import

  Time
  LP
  Sitcalc

export

  Natural
  Poss
  Agent
  Holds
  Action

define

  proc {IsAgent A}
    choice  A = jim
    []      A = joe
    []      A = jon
    end
  end

  proc {IsNatural Act}
    choice  Act = ring_timer(_)
    []      Act = end_task(_)
    end
  end

  proc{IsExog Act}
    {IsNatural Act}
  end

  proc {IsTask Tsk}
    choice Cont in Tsk=mix(Cont _) {ObjIsType Cont container}
    []     Cont in Tsk=chop(Cont) {ObjIsType Cont container}
    end
  end

  proc {IsPrimObjT Obj Type}
    choice Type=knife {IsMember Obj [knife1 knife2 knife3]}
    []     Type=bowl {IsMember Obj [bowl1 bowl2 bowl3]}
    []     Type=board {IsMember Obj [board1 board2]}
    []     Type=oven {IsMember Obj [oven1]}
    []     Type=flour {IsMember Obj [flour1 flour2 flour3 flour4 flour5]}
    []     Type=sugar {IsMember Obj [sugar1 sugar2 sugar3 sugar4 sugar5]}
    []     Type=egg {IsMember Obj [egg1 egg2 egg3]}
    []     Type=tomato {IsMember Obj [tomato1 tomato2]}
    []     Type=lettuce {IsMember Obj [lettuce1]}
    []     Type=carrot {IsMember Obj [carrot1 carrot2 carrot3]}
    end
  end

  proc {IsPrimObj Obj}
    {IsPrimObjT Obj _}
  end

  proc {IsSuperType Type SType}
    choice SType=container {IsMember Type [bowl board oven]}
    []     SType=ingredient
           {IsMember Type [flour egg sugar tomato lettuce carrot]}
    end
  end

  proc {ObjIsType Obj Type}
    choice  {IsPrimObjT Obj Type}
    []      SubType in {IsSuperType SubType Type} {ObjIsType Obj SubType}
    end
  end

  proc {IsAction Act}
    choice Agt Obj in Act=acquire_object(Agt Obj)
                      {IsAgent Agt}  {IsPrimObj Obj}
    []     Agt Obj in Act=release_object(Agt Obj)
                      {IsAgent Agt}  {IsPrimObj Obj}
    []     Agt in Act=set_timer(Agt _ _) {IsAgent Agt}
    []     Act=ring_timer(_)
    []     Agt Conts Dest in Act=place_in(Agt Conts Dest)
                             {IsAgent Agt} {IsPrimObj Conts}
                             {ObjIsType Dest container}
    []     Agt Source Dest in Act=transfer(Agt Source Dest)
                              {IsAgent Agt} {ObjIsType Source container}
                              {ObjIsType Dest container}
    []     Agt Tsk in Act=begin_task(Agt Tsk)
                       {IsAgent Agt} {IsTask Tsk}
    []     Agt Tsk in Act=end_task(Agt Tsk)
                       {IsAgent Agt} {IsTask Tsk}
    end
  end


  proc {Poss A T S}
    skip
  end

  proc {Holds F S}
    skip
  end
end

