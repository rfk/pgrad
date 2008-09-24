
functor 

import

  LP
  Time
  Sitcalc
  System

export

  IsNatural
  IsAction
  IsAgent
  IsExog
  IsFluent

  Poss
  Conflicts
  ssa: SSA
  Init

define

  proc {IsAgent A}
    choice  A = jim
    []      A = joe
    []      A = jon
    end
  end

  proc {IsTask Tsk}
    choice Cont in Tsk=mix(Cont _) {ObjIsType Cont container}
    []     Cont in Tsk=chop(Cont) {ObjIsType Cont container}
    end
  end

  proc {IsPrimObjT Obj Type}
    choice Type=knife {LP.member Obj [knife1 knife2 knife3]}
    []     Type=bowl {LP.member Obj [bowl1 bowl2 bowl3]}
    []     Type=board {LP.member Obj [board1 board2]}
    []     Type=oven {LP.member Obj [oven1]}
    []     Type=flour {LP.member Obj [flour1 flour2 flour3 flour4 flour5]}
    []     Type=sugar {LP.member Obj [sugar1 sugar2 sugar3 sugar4 sugar5]}
    []     Type=egg {LP.member Obj [egg1 egg2 egg3]}
    []     Type=tomato {LP.member Obj [tomato1 tomato2]}
    []     Type=lettuce {LP.member Obj [lettuce1]}
    []     Type=carrot {LP.member Obj [carrot1 carrot2 carrot3]}
    end
  end

  proc {IsPrimObj Obj}
    {IsPrimObjT Obj _}
  end

  proc {IsSuperType Type SType}
    choice SType=container {LP.member Type [bowl board oven]}
    []     SType=ingredient
           {LP.member Type [flour egg sugar tomato lettuce carrot]}
    end
  end

  proc {ObjIsType Obj Type}
    choice  {IsPrimObjT Obj Type}
    []      SubType in {IsSuperType SubType Type} {ObjIsType Obj SubType}
    end
  end

  proc {IsAction Act}
    choice Agt Obj in Act=acquire(Agt Obj)
                      {IsAgent Agt}  {IsPrimObj Obj}
    []     Agt Obj in Act=release(Agt Obj)
                      {IsAgent Agt}  {IsPrimObj Obj}
    []     Agt in Act=setTimer(Agt _ _) {IsAgent Agt}
    []     Act=ringTimer(_)
    []     Agt Conts Dest in Act=placeIn(Agt Conts Dest)
                             {IsAgent Agt} {IsPrimObj Conts}
                             {ObjIsType Dest container}
    []     Agt Source Dest in Act=transfer(Agt Source Dest)
                              {IsAgent Agt} {ObjIsType Source container}
                              {ObjIsType Dest container}
    []     Agt Tsk in Act=beginTask(Agt Tsk)
                       {IsAgent Agt} {IsTask Tsk}
    []     Agt Tsk in Act=endTask(Agt Tsk)
                       {IsAgent Agt} {IsTask Tsk}
    end
  end

  proc {IsNatural Act}
    choice  Act = ringTimer(_)
    []      Act = endTask(_)
    end
    {IsAction Act}
  end

  proc{IsExog Act}
    {IsNatural Act}
  end

  proc {IsFluent F}
    Agt Obj Conts RemTime ID
  in
    choice F = hasObject(Agt Obj)
           {IsAgent Agt}
           {IsPrimObj Obj}
    []     F = used(Obj)
           {ObjIsType Obj ingredient}
    []     F = timerSet(ID RemTime)
    []     F = contents(Obj Conts)
           {ObjIsType Obj container}
    []     F = doingTask(Agt Obj RemTime)
           {IsAgent Agt} {IsPrimObj Obj}
    end
  end

  proc {Poss A T S}
    {Time.decl T}
    choice A=nil fail
    []  Agt Obj in A=acquire(Agt Obj)
                   {Sitcalc.holds neg(ex(agt hasObject(agt Obj))) S}
                   {Sitcalc.holds neg(ex(t ex(m doingTask(Agt t m)))) S}
                   {Sitcalc.holds neg(used(Obj)) S}
    []  Agt Obj in A=release(Agt Obj)
                   {Sitcalc.holds hasObject(Agt Obj) S}
                   {Sitcalc.holds neg(ex(t ex(m doingTask(Agt t m)))) S}
    []  Agt ID in A=setTimer(Agt ID _)
                  {Sitcalc.holds neg(ex(id timerSet(ID id))) S}
                  {Sitcalc.holds neg(ex(t ex(m doingTask(Agt t m)))) S}
    []  ID in A=ringTimer(ID)
              {Sitcalc.holds timerSet(ID T) S}
    []  Agt Conts Dest in A=placeIn(Agt Conts Dest)
                          {Sitcalc.holds hasObject(Agt Conts) S}
                          {Sitcalc.holds hasObject(Agt Dest) S}
                          {Sitcalc.holds neg(ex(t ex(m doingTask(Agt t m)))) S}
    []  Agt Source Dest in A=transfer(Agt Source Dest)
                           {Sitcalc.holds hasObject(Agt Source) S}
                           {Sitcalc.holds hasObject(Agt Dest) S}
                           {Sitcalc.holds neg(ex(t ex(m doingTask(Agt t m)))) S}
    []  Agt Cont in A=beginTask(Agt mix(Cont _))
                    {Sitcalc.holds hasObject(Agt Cont) S}
                    {Sitcalc.holds neg(ex(t ex(m doingTask(Agt t m)))) S}
    []  Agt Cont in A=beginTask(Agt chop(Cont))
                    {Sitcalc.holds hasObject(Agt Cont) S}
                    {Sitcalc.holds neg(ex(t ex(m doingTask(Agt t m)))) S}
                    % TODO: more here - on a board, holding a knife, etc
    [] Agt Tsk RemTime in A=endTask(Agt Tsk)
                  {Sitcalc.holds doingTask(Agt Tsk RemTime) S}
                  T = {Sitcalc.start S} + RemTime
    end
  end

  proc {Conflicts C T S}
    A1 A2
  in
    {LP.member A1 C}
    {LP.member A2 C}
    not A1 = A2 end
    choice % Agents cannot do two things at once
           {Sitcalc.actor A1} = {Sitcalc.actor A2}
    []     % Agents cannot acquire the same object
           Obj in
           A1=acquire(_ Obj)
           A2=acquire(_ Obj)
           not {Sitcalc.actor A1} = {Sitcalc.actor A2} end
    end
  end

  proc {SSA F C T S}
    case F of hasObject(Agt Obj) then 
             choice {LP.member acquire(Agt Obj) C}
             [] {Sitcalc.holds F S}
                {Sitcalc.holds neg(used(Obj)) res(C T S)}
                {LP.neg proc{$}
                    {LP.member release(Agt Obj) C}
                end}
             end
    []  used(Obj) then {ObjIsType Obj ingredient}
                       choice {Sitcalc.holds used(Obj) S}
                       [] {LP.member placeIn(_ Obj _) C}
                       end
    []  timerSet(ID RemTime) then
             choice {LP.member setTimer(_ ID RemTime) C}
             []  OldRem in
                 {Sitcalc.holds timerSet(ID OldRem) S}
                 RemTime = OldRem - (T - {Sitcalc.start S})
                 {LP.neg proc {$}
                   {LP.member ringTimer(ID) C}
                 end}
             end 
    []   contents(Obj Conts) then
             choice % All the ways it can become true...
                 choice % It was previously empty, and contents were added
                     {Sitcalc.holds neg(ex(c contents(Obj c))) S}
                     choice Obj2 in {LP.member transfer(_ Obj2 Obj) C}
                                    {Sitcalc.holds contents(Obj2 Conts) S}
                     []     {LP.member placeIn(_ Conts Obj) C}
                     end
                 []  % It previously had contents, which have been added to
                     OldConts1 OldConts NewConts in
                     {Sitcalc.holds contents(Obj OldConts1) S}
                     choice Obj2 in {LP.member transfer(_ Obj2 Obj) C}
                                    {Sitcalc.holds contents(Obj2 NewConts) S}
                     []     {LP.member placeIn(_ NewConts Obj) C}
                     end
                     if OldConts1 == _|_ then OldConts = OldConts1
                     else OldConts = [OldConts1] end
                     {LP.union OldConts NewConts Conts}
                 % TODO: mixing, chopping, etc
                 end
             [] % All the ways it can become false
                {Sitcalc.holds contents(Obj Conts) S}
                {LP.neg proc {$} {LP.member transfer(_ Obj _) C} end}
                {LP.neg proc {$} Obj2 in
                    {LP.member transfer(_ Obj2 Obj) C}
                    {Sitcalc.holds contents(Obj2 _) S}
                end}
                {LP.neg proc {$} {LP.member placeIn(_ _ Obj) C} end}
                % TODO: mixing, chopping, etc
            end
    []   doingTask(Agt Tsk RemTime) then
            choice {LP.member beginTask(Agt Tsk) C}
                   % TODO: definable task duration
                   RemTime=3
            []   OldRem in
                 {Sitcalc.holds doingTask(Agt Tsk OldRem) S}
                 RemTime = OldRem - (T - {Sitcalc.start S})
                 {LP.neg proc {$} {LP.member endTask(Agt Tsk) C} end}
            end
    else {StaticFluent F} end
  end

  proc {Init F}
    {StaticFluent F}
  end

  proc {StaticFluent F}
    case F of objIsType(Obj Type) then
             {ObjIsType Obj Type}
    []   isAgent(Agt) then
            {IsAgent Agt}
    else fail end
  end

end

