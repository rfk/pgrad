%
%  Goloz.oz
%
%  Top-level implementation of MIndiGolog semantics in Oz.  We operate
%  over 'executions' rather than situations, which encode more information.
%

functor 

import

  LP
  Program
  Sitcalc

define

  %
  %  Trans(D,E,Dp,Ep)
  %
  %  Transition function for executing a single step of a program.
  %  This predicate is true when the program D, given that the current
  %  run of execution is E, can make a single step to produce the new
  %  execution Ep, with program Dp remaining to be executed.
  %
  proc {Trans D E Dp Ep}
    case D of 
        nil then fail
    []  test(Cond) then
          {HoldsEx.yes Cond E}
          Dp = nil
          Ep = ex(test:Cond action:nil thred:nil)|E
    []  seq(D1 D2) then
          choice
              D1p in {Trans D1 E D1p Ep}
              Dp = seq(D1p D2)
          []  {Final D1 E}
              {Trans D2 E Dp Ep}
          end
    []  either(D1 D2) then
          choice
              {Trans D1 E Dp Ep}
          []  {Trans D2 E Dp Ep}
          end
    []  pick(V D1) then
          local D2 in
            {LP.subInTerm V _ D1 D2}
            {Trans D2 E Dp Ep}
          end
    []  star(D1) then
          local D2 in 
            {Trans D E D2 Ep}
            Dp = seq(D2 star(D1))
          end
    []  ifte(Cond D1 D2) then
          choice
              {HoldsEx.yes Cond E}
              {Trans D1 E Dp Ep}
          []  {HoldsEx.no Cond E}
              {Trans D2 E Dp Ep}
          end
    []  wloop(Cond D1) then
          local D2 in
            {HoldsEx.yes Cond E}
            {Trans D1 E D2 Ep}
            Dp = seq(D2 wloop(Cond D1))
          end
    []  conc(D1 D2) then
          choice
              D1p EpH EpT in
              {Trans D1 E D1p EpH|EpT}
              Dp = conc(D1p D2)
              Ep = ex(test:EpH.test action:EpH.action thred:[1|EpH.thred])|EpT
          []  D2p EpH EpT in
              {Trans D2 E D2p EpH|EpT}
              Dp = conc(D1 D2p)
              Ep = ex(test:EpH.test action:EpH.action thred:2|EpH.thred)|EpT
          end
    []  pconc(D1 D2) then
          choice
              D1p in {Trans D1 E D1p Ep} 
              Dp = pconc(D1p D2)
          []  D2p in {Trans D2 E D2p Ep}
              Dp = pconc(D1 D2p)
              {LP.neg proc {$} {Trans D1 E _ _} end}
          end
    []  cstar(D1) then
          local D2 in
            {Trans D1 E D2 Ep}
            Dp = conc(D2 cstar(D1))
          end
    []  pcall(D1) then
          local Body in
            {Program.procDef D1 Body}
            {Trans Body E Dp Ep}
          end
    else local Act in 
          Act = D
          Dp = nil
          Ep = ex(test:nil action:Act thred:nil)|E
         end
    end
  end

  proc {MakePlanRec D E PAcc P}
    choice
        {Final D E}
        P = PAcc
    []  Dr Er in
        {Trans D E Dr Er}
        {Sitcalc.extendPlan E PAcc Er P}
        {Sitcalc.forEachBranch proc {$ B Pb} {MakePlanRec Dr Er B Pb} end}
    end
  end

  proc {MakePlan D P}
    {MakePlanRec D nil nil P}
  end
  MakePlan = MakePlan


  HoldsEx = holds(yes: proc {$} skip end
                  no:  proc {$} skip end)

  proc {Final D E}
    skip
  end

end

