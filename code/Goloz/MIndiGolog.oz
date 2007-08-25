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
          {Sitcalc.ex.holds.yes Cond E}
          Dp = nil
          Ep = {Sitcalc.ex.append ex(test:Cond action:nil) E}
    []  seq(D1 D2) then
          dis D1p in {Trans D1 E D1p Ep}
              Dp = seq(D1p D2)
          []  {Final D1 E}
              {Trans D2 E Dp Ep}
          end
    []  either(D1 D2) then
          dis {Trans D1 E Dp Ep}
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
          dis
              {Sitcalc.ex.holds.yes Cond E}
              {Trans D1 E Dp Ep}
          []  {Sitcalc.ex.holds.no Cond E}
              {Trans D2 E Dp Ep}
          end
    []  wloop(Cond D1) then
          local D2 in
            {Sitcalc.ex.holds.yes Cond E}
            {Trans D1 E D2 Ep}
            Dp = seq(D2 wloop(Cond D1))
          end
    []  conc(D1 D2) then
          dis D1p E1p in
              {Trans D1 E D1p E1p}
              Dp = conc(D1p D2)
              Ep = {Sitcalc.ex.thred 1 E1p}
          []  D2p E2p in
              {Trans D2 E D2p E2p}
              Dp = conc(D1 D2p)
              Ep = {Sitcalc.ex.thred 2 E2p}
          end
    []  pconc(D1 D2) then Res in
          % Use LP.ifNot to avoid re-computation on D1
          {LP.ifNot proc {$ Res1} D1p E1p in
                      {Trans D1 E D1p E1p}
                      Res1 = pconc(D1p D2)#E1p
                    end
                    proc {$ Res2} D2p E2p in
                      {Trans D2 E D2p E2p}
                      Res2 = pconc(D1 D2p)#E2p
                    end
                    Res}
          Res = Dp#Ep
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
          Ep = {Sitcalc.ex.append ex(test:nil action:Act) E}
         end
    end
  end

  proc {MakePlanRec D E PAcc P}
    dis
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

  proc {Final D E}
    skip
  end

end

