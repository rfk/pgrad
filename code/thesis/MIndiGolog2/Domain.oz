%
%  Domain.oz:  procedures specifying the details of the domain
%

functor 

import

  Sitcalc at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Sitcalc.ozf'
  LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
  Time at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Time.ozf'

export

  IsAction
  IsAgent

  Poss
  Conflicts
  Outcome
  Indep
  ssa: SSA
  Init

define

  proc {IsAgent A}
    choice  A = jim
    []      A = joe
    []      A = jon
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
    []     Agt Conts Dest in Act=placeIn(Agt Conts Dest)
                             {IsAgent Agt} {IsPrimObj Conts}
                             {ObjIsType Dest container}
    []     Agt Source Dest in Act=transfer(Agt Source Dest)
                              {IsAgent Agt} {ObjIsType Source container}
                              {ObjIsType Dest container}
    []     Agt Cont in Act=chop(Agt Cont)
                       {IsAgent Agt} {ObjIsType Cont container}
    []     Agt Cont in Act=mix(Agt Cont)
                       {IsAgent Agt} {ObjIsType Cont container}
    []     Agt Type in Act=checkFor(Agt Type)
                       {IsAgent Agt} {IsPrimObjT _ Type}
    end
  end

  proc {Poss A H}
    choice A=nil fail
    []  Agt Obj in A=acquire(Agt Obj)
                   {Sitcalc.holds neg(ex(agt hasObject(agt Obj))) H}
                   {Sitcalc.holds neg(used(Obj)) H}
    []  Agt Obj in A=release(Agt Obj)
                   {Sitcalc.holds hasObject(Agt Obj) H}
    []  Agt Conts Dest in A=placeIn(Agt Conts Dest)
                          {Sitcalc.holds hasObject(Agt Conts) H}
                          {Sitcalc.holds hasObject(Agt Dest) H}
    []  Agt Source Dest in A=transfer(Agt Source Dest)
                           {Sitcalc.holds hasObject(Agt Source) H}
                           {Sitcalc.holds hasObject(Agt Dest) H}
    []  Agt Cont in A=mix(Agt Cont)
                    {Sitcalc.holds hasObject(Agt Cont) H}
    []  Agt Cont in A=chop(Agt Cont)
                    {Sitcalc.holds hasObject(Agt Cont) H}
                    % TODO: more here - on a board, holding a knife, etc
    []  Agt Type in A=checkFor(Agt Type)
                    skip
    end
  end

  proc {Conflicts C S}
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

  proc {Indep A1 A2 B}
    if A1.1 == A2.1 then B=false
    else
      B = for return:R default:true Agr1 in {Record.toList A1} do
            for Arg2 in {Record.toList A2} do
              if Arg2 == Arg2 then {R false} end
            end
          end
    end
  end

  proc {SSA F C SR H}
    case F of hasObject(Agt Obj) then 
             choice {LP.member acquire(Agt Obj) C}
             [] {Sitcalc.holdsR F SR H}
                {LP.neg proc {$}
                  {ObjIsType Obj ingredient}
                  {LP.member placeIn(_ Obj _) C}
                end}
                {LP.neg proc {$}
                  {LP.member release(Agt Obj) C}
                end}
             end
    []  used(Obj) then {ObjIsType Obj ingredient}
                       choice {Sitcalc.holdsR used(Obj) SR H}
                       [] {LP.member placeIn(_ Obj _) C}
                       end
    []   contents(Obj Conts) then
             choice OldConts NewConts Obj2 in
                 choice
                     {LP.member placeIn(_ NewConts Obj) C}
                     OldConts = {LP.ifNot
                         proc {$ OC} Conts1 in
                           {Sitcalc.holdsR contents(Obj Conts1) {LP.copyTerm SR} {LP.copyTerm H}}
                           if Conts1 == _|_ then OC = Conts1
                           else OC = [Conts1] end
                         end
                         proc {$ OC}
                           OC = nil
                         end
                     }
                     Conts = {LP.union OldConts NewConts}
                 []  {LP.member transfer(_ Obj2 Obj) C}
                     {Sitcalc.holdsR contents(Obj2 NewConts) SR H}
                     OldConts = {LP.ifNot
                         proc {$ OC} Conts1 in
                           {Sitcalc.holdsR contents(Obj Conts1) {LP.copyTerm SR} {LP.copyTerm H}}
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
                {Sitcalc.holdsR contents(Obj Conts) SR H}
                {LP.neg proc {$} 
                    {LP.member transfer(_ Obj _) C}
                end}
                {LP.neg proc {$} Obj2 in
                    {LP.member transfer(_ Obj2 Obj) C}
                    {Sitcalc.holdsR contents(Obj2 _) {LP.copyTerm SR} {LP.copyTerm H}}
                end}
                {LP.neg proc {$} 
                    {LP.member placeIn(_ _ Obj) C}
                end}
             end
    else {StaticFact F} end
  end

  proc {Init F SR}
    case F of used(Obj) then
      
    else
      {StaticFact F}
    end
  end

  proc {StaticFact F}
    case F of objIsType(Obj Type) then
             {ObjIsType Obj Type}
    []   isAgent(Agt) then
            {IsAgent Agt}
    else fail end
  end

end

