%
%  MIndiGolog.oz:  implementation of MIndiGolog semantics
%
%  This functor implements the MIndiGolog semantics as a pair of
%  procedures Trans() and Final().  Rather than operating over ordinary
%  situation terms, they accept a run as the "current situation" and
%  return a step indicating the next action to be performed.
%

functor 

import

  LP at '../Utils/LP.ozf'
  Program at '../Program.ozf'
  SitCalc
  Step

export

  Trans
  Trans1
  Final

define

  %
  %  Transition function for executing a single step of a program.
  %  This predicate succeeds when the program D, given that the current
  %  run of execution is R, can make a single step of execution Sp
  %  leaving program Dp remaining to be executed.
  %
  proc {Trans D R Dp Sp}
    case D of 
        nil then fail
    []  test(Cond) then
          {SitCalc.holds R Cond}
          Dp = nil
          Sp = {Step.init step(test:Cond)}
    []  seq(D1 D2) then
          choice {Final D1 R}
              {Trans D2 R Dp Sp}
          []  D1p in Dp = seq(D1p D2)
              {Trans D1 R D1p Sp}
          end
    []  either(D1 D2) then
          choice {Trans D1 R Dp Sp}
          []  {Trans D2 R Dp Sp}
          end
    []  pick(V D1) then
          local D2 in
            {LP.subInTerm V _ D1 D2}
            {Trans D2 R Dp Sp}
          end
    []  star(D1) then
          local D2 in 
            {Trans D R D2 Sp}
            Dp = seq(D2 star(D1))
          end
    []  ifte(Cond D1 D2) then Sp2 in
          choice
              {SitCalc.holds R Cond}
              {Trans D1 R Dp Sp2}
              {Step.addtest Sp2 Cond Sp}
          []  {SitCalc.holds R neg(Cond)}
              {Trans D2 R Dp Sp2}
              {Step.addtest Sp2 neg(Cond) Sp}
          end
    []  wloop(Cond D1) then Sp2 in
          local D2 in
            {SitCalc.holds R Cond}
            {Trans D1 R D2 Sp2}
            {Step.addtest Sp2 Cond Sp}
            Dp = seq(D2 wloop(Cond D1))
          end
    []  conc(D1 D2) then
          choice D1p S1p in
              {Trans D1 R D1p S1p}
              Dp = conc(D1p D2)
              Sp = {Step.addthred S1p 1}
          []  D2p S2p in
              {Trans D2 R D2p S2p}
              Dp = conc(D1 D2p)
              Sp = {Step.addthred S2p 2}
          end
    []  pconc(D1 D2) then Res in
          % Use LP.ifNot to avoid re-computation on D1
          % TODO: ensure that D1 contains no free variables
          {LP.ifNot proc {$ Res1} D1p S1p in
                      {Trans D1 R D1p S1p}
                      Res1 = pconc(D1p D2)#S1p
                    end
                    proc {$ Res2} D2p S2p in
                      {Trans D2 R D2p S2p}
                      Res2 = pconc(D1 D2p)#S2p
                    end
                    Res}
          Dp#Sp = Res
    []  cstar(D1) then
          local D2 in
            {Trans D1 R D2 Sp}
            Dp = conc(D2 cstar(D1))
          end
    []  pcall(D1) then
          local Body in
            {Program.procDef D1 Body}
            {Trans Body R Dp Sp}
          end
    else local Act in 
          % TODO: proper MIndiGolog semantics for individual actions
          Act = D
          Dp = nil
          Sp = {Step.init step(action:Act)}
         end
    end
  end

  %
  %  Termination function for executing a program.
  %  This predicate succeeds when the program D can legally terminate
  %  when the current run of execution is R.
  %
  proc {Final D R}
   case D of
       nil then skip
   []  seq(D1 D2) then {Final D1 R} {Final D2 R}
   []  either(D1 D2) then choice {Final D1 R} [] {Final D2 R} end
   []  pick(V D1) then local D2 in {LP.subInTerm V _ D1 D2} {Final D2 R} end
   []  star(_) then skip
   []  ifte(Cond D1 D2) then
               choice  {SitCalc.holds R Cond} {Final D1 R}
               []   {SitCalc.holds R neg(Cond)} {Final D2 R}
               end
   []  wloop(Cond D1) then choice {SitCalc.holds R neg(Cond)} 
                           [] {Final D1 R} end
   []  conc(D1 D2) then {Final D1 R} {Final D2 R}
   []  pconc(D1 D2) then {Final D1 R} {Final D2 R}
   []  cstar(_) then skip
   []  pcall(D1) then local Body in {Program.procDef D1 Body} {Final Body R} end
   else fail
   end
  end


  %
  %  Find a non-empty transition step of the program D in run R.
  %  Empty steps (e.g. for test() conditions) cannot show up in a
  %  joint plan, but they do appear in individual runs and can
  %  affect the ordering among other steps.  This procedure collects
  %  any empty transitions in the local run until it finds a step
  %  bearing an action, which it returns along with the updated run.
  %
  proc {Trans1 D R Dp Rp S}
    Dr Sr
  in
    {Trans D R Dr Sr}
    if Sr.action == nil then
      {Trans1 Dr ex(Sr R) Dp Rp S}
    else
      Dp=Dr Rp=R S=Sr
    end
  end


end
