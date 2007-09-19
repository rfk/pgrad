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

  LP
  Program
  Sitcalc at 'SitCalc/SitCalc.ozf'
  PlanFront

export

  Trans
  Step
  Steps
  Final
  Plan
  JointPlan

  Test

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
          {Sitcalc.ex.holds Cond E true}
          Dp = nil
          Ep = {Sitcalc.ex.append E step(test:Cond)}
    []  seq(D1 D2) then
          choice D1p in {Trans D1 E D1p Ep}
              Dp = seq(D1p D2)
          []  {Final D1 E}
              {Trans D2 E Dp Ep}
          end
    []  either(D1 D2) then
          choice {Trans D1 E Dp Ep}
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
    []  ifte(Cond D1 D2) then Ep2 in
          choice
              {Sitcalc.ex.holds Cond E true}
              {Trans D1 E Dp Ep2}
              {Sitcalc.ex.addtest Ep2 Cond Ep}
          []  {Sitcalc.ex.holds neg(Cond) E true}
              {Trans D2 E Dp Ep2}
              {Sitcalc.ex.addtest Ep2 neg(Cond) Ep}
          end
    []  wloop(Cond D1) then Ep2 in
          local D2 in
            {Sitcalc.ex.holds Cond E true}
            {Trans D1 E D2 Ep2}
            {Sitcalc.ex.addtest Ep2 Cond Ep}
            Dp = seq(D2 wloop(Cond D1))
          end
    []  conc(D1 D2) then
          choice D1p E1p in
              {Trans D1 E D1p E1p}
              Dp = conc(D1p D2)
              Ep = {Sitcalc.ex.addthred E1p 1}
          []  D2p E2p in
              {Trans D2 E D2p E2p}
              Dp = conc(D1 D2p)
              Ep = {Sitcalc.ex.addthred E2p 2}
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
          Dp#Ep = Res
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
          Ep = {Sitcalc.ex.append E step(action:Act)}
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
               choice  {Sitcalc.ex.holds Cond E true} {Final D1 E}
               []   {Sitcalc.ex.holds neg(Cond) E true} {Final D2 E}
               end
   []  wloop(Cond D1) then choice {Sitcalc.ex.holds neg(Cond) E true} 
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


  %
  %  Determine a single step of execution of program D in execution E.
  %  This differs from {Trans} in that {Trans} may make a transition
  %  without performing an action, while {Step} will guarantee that an
  %  action is performed.
  %
  proc {Step D E Dr Er}
    Ep Dp
  in
    {Trans D E Dp Ep}
    if {Sitcalc.ex.actions Ep}=={Sitcalc.ex.actions E} then
      {Step Dp Ep Dr Er}
    else
      Dr=Dp Er=Ep
    end
  end

  proc {Steps N D E Dr Er}
    if N == 0 then Dr = D Er = E
    else Dp Ep in
      {Step D E Dp Ep}
      {Steps N-1 Dp Ep Dr Er}
    end
  end

  proc {Plan D EIn EOut}
    choice
       {Final D EIn} EIn = EOut
    [] Dr Er in {Trans D EIn Dr Er} {Plan Dr Er EOut}
    end
  end

  %
  %  Search for a join plan executing program D in the current situation.
  %  To do so, construct a closed PlanFront starting from now#D#JP
  %
  proc {JointPlan D JP}
    {ClosePlanFront {PlanFront.init now#D#JP} _}
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
    E#D#_ = {PlanFront.select PFIn}
    Ep Matching NewOpen NewClosed PF2 PF3
  in
    {Step D E _ Ep}
    Matching = {PlanFront.matching PFIn E {Sitcalc.actors Ep.1.action}}
    {ExpandExecutions Matching Ep.1.action NewOpen NewClosed}
    PF2 = {PlanFront.remove PFIn Matching}
    PF3 = {PlanFront.addOpen PF2 NewOpen}
    PFOut = {PlanFront.addClosed PF3 NewClosed}
  end

  %
  %  For every E#D#J entry in the input list, check that it has a
  %  step compatible with the given action and add all possible executions
  %  using that step to the appropriate output list.
  %
  proc {ExpandExecutions Ins Action OutOpen OutClosed}
    case Ins of E#D#J|InsT then OutOT OutCT Dp Ep Branches in
      {Step D E Dp Ep}
      Ep.1.action = Action
      Branches = {Sitcalc.jplan.extend J E}
      {AssignBranchesToList Branches Dp OutOpen OutClosed OutOT OutCT}
      {ExpandExecutions InsT Step OutOT OutCT}
    else OutOpen=nil OutClosed=nil end
  end

  proc {AssignBranchesToList Branches D Open Closed OpenT ClosedT}
    case Branches of E#J|Bs then Open1 Closed1 in
      if {IsFinal D E} then
        Open = Open1
        Closed = (E#D#J)|Closed1
      else
        Open = (E#D#J)|Open1
        Closed = Closed1
      end
      {AssignBranchesToList Bs D Open1 Closed1 OpenT ClosedT}
    else OpenT=Open ClosedT=Closed end
  end

  proc {Test}
    skip
  end

end
