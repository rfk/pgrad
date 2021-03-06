%
%  MIndiGolog.oz:  implementation of MIndiGolog semantics
%
%  Copyright 2008, Ryan Kelly
%
%  This functor implements the MIndiGolog semantics as a pair of
%  procedures Trans() and Final().  Rather than operating over ordinary
%  situation terms, they accept a run as the "current situation" and
%  return a step indicating the next action to be performed.
%
%  The operators are constructed using the following record labels, some of
%  which are non-standard to avoid conflicts with Oz keywords:
%
%    seq(D1 D2)       - sequential execution
%    test(C)          - test condition
%    choose(D1 D2)    - nondeterministic choice of program
%    pick(V D1)       - nondeterministic choice of argument
%    star(D1)         - nondeterministic iteration
%    ifte(C D1 D2)    - if-then-else
%    wloop(C D1)      - while-loop
%    conc(D1 D2)      - concurrent program execution
%    pconc(D1 D2)     - prioritised concurrent execution
%    cstar(D1)        - concurrent iteration
%    pcall(P)         - procedure call
%    search(D)        - search for offline execution
%    dosteps(S)       - execute pre-planned list of actions
%

functor 

import

  LP
  Procedures
  Sitcalc
  Step

  Search

export

  Trans
  Trans1
  Final
  IsFinal

define

  %
  %  Transition function for executing a single step of a program.
  %  This predicate succeeds when the program D, given that the current
  %  run of execution is R, can make a single step of execution Sp
  %  leaving program Dp remaining to be executed.
  %
  proc {Trans D H Dp Sp}
    case D of 
        nil then fail
    []  test(Cond) then
          {Sitcalc.holds Cond H}
          Dp = nil
          Sp = {Step.init step(test:Cond)}
    []  seq(D1 D2) then
          choice {Final D1 H}
              {Trans D2 H Dp Sp}
          []  D1p in Dp = seq(D1p D2)
              {Trans D1 H D1p Sp}
          end
    []  choose(D1 D2) then
          choice {Trans D1 H Dp Sp}
          []  {Trans D2 H Dp Sp}
          end
    []  pick(V D1) then
          local D2 in
            {LP.subInTerm V _ D1 D2}
            {Trans D2 H Dp Sp}
          end
    []  star(D1) then
          local D2 in 
            {Trans D H D2 Sp}
            Dp = seq(D2 star(D1))
          end
    []  ifte(Cond D1 D2) then Sp2 in
          choice
              {Sitcalc.holds Cond H}
              {Trans D1 H Dp Sp2}
              {Step.addtest Sp2 Cond Sp}
          []  {Sitcalc.holds neg(Cond) H}
              {Trans D2 H Dp Sp2}
              {Step.addtest Sp2 neg(Cond) Sp}
          end
    []  wloop(Cond D1) then Sp2 in
          local D2 in
            {Sitcalc.holds Cond H}
            {Trans D1 H D2 Sp2}
            {Step.addtest Sp2 Cond Sp}
            Dp = seq(D2 wloop(Cond D1))
          end
    []  conc(D1 D2) then
          choice D1p S1p in
              {Trans D1 H D1p S1p}
              Dp = conc(D1p D2)
              Sp = {Step.addthred S1p l}
          []  D2p S2p in
              {Trans D2 H D2p S2p}
              Dp = conc(D1 D2p)
              Sp = {Step.addthred S2p r}
          end
    []  pconc(D1 D2) then Res in
          % Use LP.ifNot to avoid re-computation on D1
          % TODO: ensure that D1 contains no free variables
          {LP.ifNot proc {$ Res1} D1p S1p in
                      {Trans D1 H D1p S1p}
                      Res1 = pconc(D1p D2)#S1p
                    end
                    proc {$ Res2} D2p S2p in
                      {Trans D2 H D2p S2p}
                      Res2 = pconc(D1 D2p)#S2p
                    end
                    Res}
          Dp#Sp = Res
    []  cstar(D1) then
          local D2 in
            {Trans D1 H D2 Sp}
            Dp = conc(D2 cstar(D1))
          end
    []  pcall(D1) then
          local Body in
            {Procedures.procdef D1 Body}
            {Trans Body H Dp Sp}
          end
    else local Act in 
          Act = D
          Dp = nil
          {Sitcalc.legal [Act] H}
          Sp = {Step.init step(action:Act)}
         end
    end
  end

  %
  %  Termination function for executing a program.
  %  This predicate succeeds when the program D can legally terminate
  %  when the current run of execution is R.
  %
  proc {Final D H}
   case D of
       nil then skip
   []  seq(D1 D2) then {Final D1 H} {Final D2 H}
   []  either(D1 D2) then choice {Final D1 H} [] {Final D2 H} end
   []  pick(V D1) then local D2 in {LP.subInTerm V _ D1 D2} {Final D2 H} end
   []  star(_) then skip
   []  ifte(Cond D1 D2) then
               choice  {Sitcalc.holds Cond H} {Final D1 H}
               []   {Sitcalc.holds neg(Cond) H} {Final D2 H}
               end
   []  wloop(Cond D1) then choice {Sitcalc.holds neg(Cond) H} 
                           [] {Final D1 H} end
   []  conc(D1 D2) then {Final D1 H} {Final D2 H}
   []  pconc(D1 D2) then {Final D1 H} {Final D2 H}
   []  cstar(_) then skip
   []  pcall(D1) then local Body in {Procedures.procdef D1 Body} {Final Body H} end
   else fail
   end
  end

  %
  %  Utility function for testing whether a program is final.
  %
  proc {IsFinal D H B}
    Soln = {Search.base.one proc {$ Q} {Final D H} Q=unit end}
  in
    B = (Soln \= nil)
  end

  %
  %  Find a non-empty transition step of the program D in run R.
  %  Empty steps (e.g. for test() conditions) cannot show up in a
  %  joint plan, but they do appear in individual runs and can
  %  affect the ordering among other steps.  This procedure collects
  %  any empty transitions in the local run until it finds a step
  %  bearing an action, which it returns along with the updated run.
  %
  %  To avoid generating loads of redundant solutions, this procedure
  %  insists that chains of empty transitions be ordered according
  %  to their thred IDs.  Since empty steps do not change the state of
  %  the world or the ability to perform transitions in other threads,
  %  different orderings of them are redundant.
  %
  proc {Trans1 D H Dp Hp S}
    Dr Sr
  in
    {Trans D H Dr Sr}
    if Sr.action == nil then
      if H \= now andthen H.1.action == nil then
        {ThreadsOrdered H.1.thred Sr.thred}
      end
      {Trans1 Dr ex(Sr H) Dp Hp S}
    else
      Dp=Dr Hp=H S=Sr
    end
  end

  proc {ThreadsOrdered T1 T2}
    for break:B I1 in T1 I2 in T2 do
      if I1 \= I2 then
        (I1 < I2) = true
        {B}
      end
    end
  end

end
