%
%  MIndiGolog.oz:  implementation of MIndiGolog semantics
%
%  This functor implements the MIndiGolog semantics as a pair of
%  procedures Trans() and Final().  Rather than operating over ordinary
%  situation terms, they operate over executions to keep some additional
%  bookkeeping information.
%
%  It also exports the procedure JointPlan, a logic program searching
%  for a joint plan to execute a given program.
%

functor 

import

  LP at '../Utils/LP.ozf'
  Program at '../Program.ozf'
  SitCalc
  Execution
  Step
  JointPlan
  PlanFront

  System

export

  Trans
  Final
  MakeJointPlan

  Test

define

  %
  %  Trans(D,E,Dp,Sp)
  %
  %  Transition function for executing a single step of a program.
  %  This predicate is true when the program D, given that the current
  %  run of execution is E, can make a single step of execution Sp
  %  leaving program Dp remaining to be executed.
  %
  proc {Trans D E Dp Sp}
    case D of 
        nil then fail
    []  test(Cond) then
          {Execution.holds E Cond}
          Dp = nil
          Sp = {Step.init step(test:Cond)}
    []  seq(D1 D2) then
          choice {Final D1 E}
              {Trans D2 E Dp Sp}
          []  D1p in Dp = seq(D1p D2)
              {Trans D1 E D1p Sp}
          end
    []  either(D1 D2) then
          choice {Trans D1 E Dp Sp}
          []  {Trans D2 E Dp Sp}
          end
    []  pick(V D1) then
          local D2 in
            {LP.subInTerm V _ D1 D2}
            {Trans D2 E Dp Sp}
          end
    []  star(D1) then
          local D2 in 
            {Trans D E D2 Sp}
            Dp = seq(D2 star(D1))
          end
    []  ifte(Cond D1 D2) then Sp2 in
          choice
              {Execution.holds E Cond}
              {Trans D1 E Dp Sp2}
              {Step.addtest Sp2 Cond Sp}
          []  {Execution.holds E neg(Cond)}
              {Trans D2 E Dp Sp2}
              {Step.addtest Sp2 neg(Cond) Sp}
          end
    []  wloop(Cond D1) then Sp2 in
          local D2 in
            {Execution.holds E Cond}
            {Trans D1 E D2 Sp2}
            {Step.addtest Sp2 Cond Sp}
            Dp = seq(D2 wloop(Cond D1))
          end
    []  conc(D1 D2) then
          choice D1p S1p in
              {Trans D1 E D1p S1p}
              Dp = conc(D1p D2)
              Sp = {Step.addthred S1p 1}
          []  D2p S2p in
              {Trans D2 E D2p S2p}
              Dp = conc(D1 D2p)
              Sp = {Step.addthred S2p 2}
          end
    []  pconc(D1 D2) then Res in
          % Use LP.ifNot to avoid re-computation on D1
          {LP.ifNot proc {$ Res1} D1p S1p in
                      {Trans D1 E D1p S1p}
                      Res1 = pconc(D1p D2)#S1p
                    end
                    proc {$ Res2} D2p S2p in
                      {Trans D2 E D2p S2p}
                      Res2 = pconc(D1 D2p)#S2p
                    end
                    Res}
          Dp#Sp = Res
    []  cstar(D1) then
          local D2 in
            {Trans D1 E D2 Sp}
            Dp = conc(D2 cstar(D1))
          end
    []  pcall(D1) then
          local Body in
            {Program.procDef D1 Body}
            {Trans Body E Dp Sp}
          end
    else local Act in 
          Act = D
          Dp = nil
          % TODO: proper MIndiGolog semantics for individual actions
          Sp = {Step.init E step(action:Act)}
         end
    end
  end

  proc {Final D E}
   case D of
       nil then skip
   []  seq(D1 D2) then {Final D1 E} {Final D2 E}
   []  either(D1 D2) then choice {Final D1 E} [] {Final D2 E} end
   []  pick(V D1) then local D2 in {LP.subInTerm V _ D1 D2} {Final D2 E} end
   []  star(_) then skip
   []  ifte(Cond D1 D2) then
               choice  {Execution.holds E Cond} {Final D1 E}
               []   {Execution.holds E neg(Cond)} {Final D2 E}
               end
   []  wloop(Cond D1) then choice {Execution.holds E neg(Cond)} 
                           [] {Final D1 E} end
   []  conc(D1 D2) then {Final D1 E} {Final D2 E}
   []  pconc(D1 D2) then {Final D1 E} {Final D2 E}
   []  cstar(_) then skip
   []  pcall(D1) then local Body in {Program.procDef D1 Body} {Final Body E} end
   else fail
   end
  end

  proc {IsFinal D E B}
    try {Final D E} B = true
    catch _ then B = false end
  end

  proc {Trans1 D E Dp Sp}
  end

  %
  %  Search for a join plan executing program D in the current situation.
  %  To do so, construct a closed PlanFront starting from now#D
  %
  proc {MakeJointPlan D JP} PFOut ExOut in
    {ClosePlanFront {PlanFront.init now#D} PFOut}
    ExOut = for collect:C E#_ in PFOut.closed do
              {C E}
            end
    {JointPlan.fromExs ExOut JP}
  end

  %
  %  Expand the given PlanFront into a closed state.
  %
  proc {ClosePlanFront PFIn PFOut}
    if {PlanFront.closed PFIn} then
      PFOut = PFIn
    else
      PF2 = {ExpandPlanFront PFIn} in
      PFOut = {ClosePlanFront PF2}
    end
  end

  %
  %  Expand the given plan front by a single step.
  %  This involves selecting an open execution from the front,
  %  finding a step for it that is compatible with all other
  %  executions in the front, and updating the front with this
  %  new info.
  %
  proc {ExpandPlanFront PFIn PFOut}
    E#D = {PlanFront.select PFIn}
    Sp Matching NewOpen NewClosed PF2
  in
    {Trans1 D E _ Sp}
    PF2 = {PlanFront.popMatching PFIn E {SitCalc.actors Sp.action} Matching}
    {ExpandExecutions Matching Sp.action NewOpen NewClosed}
    PFOut = {PlanFront.push PF2 NewOpen NewClosed}
  end

  %
  %  For every E#D entry in the input list, check that it has a
  %  step compatible with the given action and add all possible executions
  %  using that step to the appropriate output list.
  %
  proc {ExpandExecutions Ins Action OutOpen OutClosed}
    case Ins of E#D|InsT then OutOT OutCT Dp Sp Branches in
      {Trans1 D E Dp Ep Sp}
      Sp.action = Action
      Branches = {Execution.outcomes Ep}
      {AssignBranchesToList Branches Dp OutOpen OutClosed OutOT OutCT}
      {ExpandExecutions InsT Action OutOT OutCT}
    else OutOpen=nil OutClosed=nil end
  end

  proc {AssignBranchesToList Branches D Open Closed OpenT ClosedT}
    case Branches of E|Bs then Open1 Closed1 in
      if {IsFinal D E} then
        Open = Open1
        Closed = (E#D)|Closed1
      else
        Open = (E#D)|Open1
        Closed = Closed1
      end
      {AssignBranchesToList Bs D Open1 Closed1 OpenT ClosedT}
    else OpenT=Open ClosedT=Closed end
  end

  proc {Test}
    skip
  end

end
