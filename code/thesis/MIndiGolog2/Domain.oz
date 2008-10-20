%
%  Domain.oz:  procedures specifying the details of the domain
%
%  Copyright 2008, Ryan Kelly
%
%  This file provides the basic procedures to define a particular domain -
%  the available actions, agents, fluents etc, along with their successor
%  state axioms and initial world state.
%
%  These definitions are for the "cooking agents" example domain used
%  throughout the thesis.
%


functor 

import

  Sitcalc
  LP

  Search

export

  IsAction
  IsAgent

  Poss
  Conflicts
  Outcome
  AddSensingResults
  Indep
  ssa: SSA
  Init

define

  %  Enumerate the agents in the domain.
  %
  proc {IsAgent A}
    choice  A = jim
    []      A = joe
    []      A = jon
    end
  end

  %  Enumerate the primitive objects and types in the domain.
  %
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
    []     Type=cheese {LP.member Obj [cheese1 cheese2]}
    end
  end

  %  Assert that <Obj> is a primitive object of unspecified type
  %
  proc {IsPrimObj Obj}
    {IsPrimObjT Obj _}
  end

  %  Constructs a simple hierarchy of object types
  %
  proc {IsSuperType Type SType}
    choice SType=container {LP.member Type [bowl board oven]}
    []     SType=ingredient
           {LP.member Type [flour egg sugar tomato lettuce carrot cheese]}
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

  %  Specify the possibility predicate for each individual action type
  %
  proc {Poss A H}
    choice A=nil fail
    []  Obj in A=acquire(_ Obj)
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
    []  A=checkFor(_ _)
    end
  end

  %  Enumerate the potential outcomes of each individual action type.
  %  This is an record whose features are agent names, and the corresponding
  %  values give the observations made by each agent.  E.g.
  %
  %     out(jon:nil jim:[chop(jim board1)] joe:nil)
  %
  proc {Outcome A O}
    case A of checkFor(Agt _) then Res Feats in
            %  checkFor yields "t" or "f", which is visible only
            %  to the performing agent.
            %
            choice Res=t [] Res=f end
            Feats = {Search.base.all proc {$ R} Agt2 in
                         {IsAgent Agt2}
                         if Agt2 == Agt then R = Agt2#[A#Res]
                         else R = Agt2#nil end
                     end}
            O = {Record.adjoinList out Feats}
    []  acquire(_ _) then Feats in
            %
            % acquire is observable by all agents
            %
            Feats = {Search.base.all proc {$ R} Agt2 in
                       {IsAgent Agt2}
                       R = Agt2#[A]
                    end}
            O = {Record.adjoinList out Feats}
    []  release(_ _) then Feats in
            %
            % release is observable by all agents
            %
            Feats = {Search.base.all proc {$ R} Agt2 in
                       {IsAgent Agt2}
                       R = Agt2#[A]
                    end}
            O = {Record.adjoinList out Feats}
    else Feats in
            %
            % all other actions are private to the performing agent
            %
            Feats = {Search.base.all proc {$ R} Agt2 in
                         {IsAgent Agt2}
                         if Agt2 == {Sitcalc.actor A} then R = Agt2#[A]
                         else R = Agt2#nil end
                     end}
            O = {Record.adjoinList out Feats}
    end
  end


  %  Add the sensing results from the given outcome into the list.
  %  When reasoning based on a history, we accumulate all sensing results
  %  into a list and use it to answer queries in the initial situation.
  %  
  proc {AddSensingResults SRIn Out SROut}
    NewRes
  in
    NewRes = for return:R default:nil Agt in {Record.arity Out} do
               case Out.Agt of [Res] then
                 %
                 %  Only checkFor(Agt Type) can give useful results
                 %
                 case Res of checkFor(_ Type)#Whether then
                   {R [Type#Whether]}
                 else skip end
               else skip end
             end
    SROut = {List.append SRIn NewRes}
  end


  %  Determine whether actions in C are in conflict, given current history H
  %
  proc {Conflicts C H}
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

  %  Determine whether two given actions are independent.
  %  In the cooking agents domain, actions are independent if they
  %  each with different objects, which we check by simply comparing their
  %  arguments in a loop.
  %
  proc {Indep A1 A2 B}
    if A1.1 == A2.1 then B=false
    else
      B = for return:R default:true Arg1 in {Record.toList A1} do
            for Arg2 in {Record.toList A2} do
              if Arg1 == Arg2 then {R false} end
            end
          end
    end
  end

  %  Successor state axioms for primitive fluents.
  %  We accumulate a list of sensing results from the given history,
  %  which will eventually be used by {Init} to answer some queries.
  %
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

  %  Check whether a primitive fluent holds initially.
  %
  %  For used(Obj), this may hold if Obj is an egg and the accumulated
  %  sensing results indicate that all eggs have been used.
  %
  proc {Init F SR}
    case F of used(Obj) then
      {IsPrimObjT Obj egg}
      {LP.member egg#f SR}
    else
      {StaticFact F}
    end
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

