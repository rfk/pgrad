%
%  Domain.oz:  procedures specifying the details of the domain
%

functor 

import

  Sitcalc at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Sitcalc.ozf'
  LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
  Time at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Time.ozf'

export

  %  Enumerate the different kinds of object
  IsNatural
  IsAction
  IsAgent
  IsExog

  %  Primitive Poss, SSA and Init defnitions
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
    []     Type=lettuce {LP.member Obj [lettuce1 lettuce2]}
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
    []      Act = endTask(_ _)
    end
    % TODO: this generates far too many choicepoints
    %{IsAction Act}
  end

  proc{IsExog Act}
    {IsNatural Act}
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
                  {Time.decl RemTime}
                  {Sitcalc.holds doingTask(Agt Tsk RemTime) S}
                  T = {Time.plus {Sitcalc.start S} RemTime}
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
                {LP.neg proc {$}
                  {LP.member {LP.copyTerm release(Agt Obj)} C}
                end}
             end
    []  used(Obj) then {ObjIsType Obj ingredient}
                       choice {Sitcalc.holds used(Obj) S}
                       [] {LP.member placeIn(_ Obj _) C}
                       end
    []  timerSet(ID RemTime) then
             choice {LP.member setTimer(_ ID RemTime) C}
             []  OldRem Dur in
                 {Sitcalc.holds timerSet(ID OldRem) S}
                 Dur = {Time.minus T {Sitcalc.start S}}
                 RemTime = {Time.minus OldRem Dur}
                 {LP.neg proc {$}
                    {LP.member {LP.copyTerm ringTimer(ID)} C}
                 end}
             end 
    []   contents(Obj Conts) then
             choice OldConts NewConts Obj2 in
                 choice
                     {LP.member placeIn(_ NewConts Obj) C}
                     OldConts = {LP.ifNot
                         proc {$ OC} Conts1 in
                           {Sitcalc.holds contents(Obj Conts1) {LP.copyTerm S}}
                           if Conts1 == _|_ then OC = Conts1
                           else OC = [Conts1] end
                         end
                         proc {$ OC}
                           OC = nil
                         end
                     }
                     Conts = {LP.union OldConts NewConts}
                 []  {LP.member transfer(_ Obj2 Obj) C}
                     {Sitcalc.holds contents(Obj2 NewConts) S}
                     OldConts = {LP.ifNot
                         proc {$ OC} Conts1 in
                           {Sitcalc.holds contents(Obj Conts1) {LP.copyTerm S}}
                           if Conts1 == _|_ then OC = Conts1
                           else OC = [Conts1] end
                         end
                         proc {$ OC}
                           OC = nil
                         end
                     }
                     Conts = {LP.union OldConts NewConts}
                 % TODO: mixing, chopping, etc
                 end
             [] % All the ways it can become false
                {Sitcalc.holds contents(Obj Conts) S}
                {LP.neg proc {$} 
                    {LP.member transfer(_ Obj _) C}
                end}
                {LP.neg proc {$} Obj2 in
                    {LP.member transfer(_ Obj2 Obj) C}
                    {Sitcalc.holds contents(Obj2 _) {LP.copyTerm S}}
                end}
                {LP.neg proc {$} 
                    {LP.member placeIn(_ _ Obj) C}
                end}
             end
    []   doingTask(Agt Tsk RemTime) then
            {Time.decl RemTime}
            choice {LP.member beginTask(Agt Tsk) C}
                   RemTime=3  %TODO: definable task duration
            []   OldRem Dur in
                 {Time.decl Dur} {Time.decl OldRem}
                 {LP.neg proc {$} Al in
                   Al = {LP.copyTerm endTask(Agt Tsk)}
                   {LP.member Al C}
                 end}
                 {Sitcalc.holds doingTask(Agt Tsk OldRem) S}
                 Dur = {Time.minus T {Sitcalc.start S}}
                 RemTime = {Time.minus OldRem Dur}
            end
    else {StaticFact F} end
  end

  proc {Init F}
    {StaticFact F}
  end

  proc {StaticFact F}
    case F of objIsType(Obj Type) then
             {ObjIsType Obj Type}
    []   isAgent(Agt) then
            {IsAgent Agt}
    else fail end
  end

end

