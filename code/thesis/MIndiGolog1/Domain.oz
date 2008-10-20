%
%  Domain.oz:  procedures specifying the details of the domain
%
%  Copyright 2008, Ryan Kelly
%
%  This file provides the basic procedures to define a particular domain -
%  the available actions, agents, fluents etc, along with their successor
%  state axioms and initial world state.
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

  %  Enumerate the agents operating in the domain
  %
  proc {IsAgent A}
    choice  A = jim
    []      A = joe
    []      A = jon
    end
  end

  %  Enumerate the long-running tasks available in the domain
  %
  proc {IsTask Tsk}
    choice Cont in Tsk=mix(Cont _) {ObjIsType Cont container}
    []     Cont in Tsk=chop(Cont) {ObjIsType Cont container}
    end
  end

  %  Enumerate primitive domain objects, and their types.
  %
  proc {IsPrimObjT Obj Type}
    choice Type=knife {LP.member Obj [knife1 knife2 knife3]}
    []     Type=bowl {LP.member Obj [bowl1 bowl2 bowl3]}
    []     Type=board {LP.member Obj [board1 board2]}
    []     Type=flour {LP.member Obj [flour1 flour2 flour3 flour4 flour5]}
    []     Type=sugar {LP.member Obj [sugar1 sugar2 sugar3 sugar4 sugar5]}
    []     Type=egg {LP.member Obj [egg1 egg2 egg3]}
    []     Type=tomato {LP.member Obj [tomato1 tomato2]}
    []     Type=lettuce {LP.member Obj [lettuce1 lettuce2]}
    []     Type=carrot {LP.member Obj [carrot1 carrot2 carrot3]}
    end
  end

  %  Assert that <Obj> is a primitive object of unspecified type.
  %
  proc {IsPrimObj Obj}
    {IsPrimObjT Obj _}
  end

  %  Constructs a simple hierarchy of object types
  %
  proc {IsSuperType Type SType}
    choice SType=container {LP.member Type [bowl board]}
    []     SType=ingredient
           {LP.member Type [flour egg sugar tomato lettuce carrot]}
    end
  end

  %  Assert that <Obj> is a primitive object of type <Type>
  %
  proc {ObjIsType Obj Type}
    choice  {IsPrimObjT Obj Type}
    []      SubType in {IsSuperType SubType Type} {ObjIsType Obj SubType}
    end
  end

  %  Enumerate the actions possible in the domain, as well as binding their
  %  arguments to objects of the appropriate type.
  %
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

  %  Identify natural actions.
  %
  proc {IsNatural Act}
    choice  Act = ringTimer(_)
    []      Act = endTask(_ _)
    end
    % TODO: this generates far too many choicepoints
    %{IsAction Act}
  end

  %  Identify exogenous actions
  %
  proc{IsExog Act}
    {IsNatural Act}
  end


  %  Specify the possibility predicate for each individual action type.
  %
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

  %  Determine whether a set of concurrent actions is in conflict.
  %
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


  %  Implement basic successor state axiom for each primitive fluent
  %  in the domain.
  %
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

  %  Determine whether a given primitive fluent holds initially.
  %
  proc {Init F}
    {StaticFact F}
  end

  %  Specify static domain facts - i.e. things that can be queried but
  %  are not fluents, and do not change as a result of actions
  %
  proc {StaticFact F}
    case F of objIsType(Obj Type) then
             {ObjIsType Obj Type}
    []   isAgent(Agt) then
            {IsAgent Agt}
    else fail end
  end

end

