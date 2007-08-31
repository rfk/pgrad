%
%  MIndiGolog.oz:  implementation of MIndiGolog semantics
%
%  This functor implements the MIndiGolog semantics as a pair of
%  procedures Trans() and Final().  Rather than operating over ordinary
%  situation terms, they operate over executions and keep some additional
%  bookkeeping information.
%
%  To support
%

functor 

import

  LP
  Program
  Sitcalc

export

  HoldsEx
  Trans
  Final
  MakePlan

define

  HoldsEx = _

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
          {HoldsEx Cond E}
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
    []  ifte(Cond D1 D2) then Ep2
          dis
              {HoldsEx Cond E}
              {Trans D1 E Dp Ep2}
              {Sitcalc.ex.addtest Ep2 Cond Ep}
          []  {HoldsEx neg(Cond) E}
              {Trans D2 E Dp Ep2}
              {Sitcalc.ex.addtest Ep2 neg(Cond) Ep}
          end
    []  wloop(Cond D1) then Ep2 in
          local D2 in
            {HoldsEx Cond E}
            {Trans D1 E D2 Ep2}
            {Sitcalc.ex.addtest Ep2 Cond Ep}
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
          Ep = {Sitcalc.ex.append ex(test:true action:Act) E}
         end
    end
  end

  proc {Final D E}
  case D of
      nil then skip
  []  seq(D1 D2) then {Final D1 E} {Final D2 E}
  []  either(D1 D2) then dis {Final D1 E} [] {Final D2 E} end
  []  pick(V D1) then local D2 in {LP.subInTerm V _ D1 D2} {Final D2 E} end
  []  star(_) then skip
  []  ifte(Cond D1 D2) then
               dis  {HoldsEx Cond E} {Final D1 E}
               []   {HoldsEx neg(Cond) E} {Final D2 E}
               end
  []  wloop(Cond D1) then dis {HoldsEx neg(Cond) E} [] {Final D1 E} end
  []  conc(D1 D2) then {Final D1 E} {Final D2 E}
  []  pconc(D1 D2) then {Final D1 E} {Final D2 E}
  []  cstar(_) then skip
  []  pcall(D1) then local Body in {Program.procDef D1 Body} {Final Body E} end
  end


  proc {MakePlanRec D E PAcc P}
    dis
        {Final D E}
        P = {Sitcalc.plan.finish PAcc}
    []  Dr Er in
        {Trans D E Dr Er}
        {Sitcalc.plan.extend E PAcc Er P}
        {Sitcalc.forEachBranch proc {$ B Pb} {MakePlanRec Dr Er B Pb} end}
    end
  end

  proc {MakePlan D E P}
    {MakePlanRec D E nil P}
  end
  MakePlan = MakePlan

end

