%
%  MIndiGolog.oz:  implementation of MIndiGolog semantics
%
%  This functor implements the MIndiGolog semantics as a pair of
%  procedures Trans() and Final().  Rather than operating over ordinary
%  situation terms, they operate over executions to keep some additional
%  bookkeeping information.
%
%  It also exports the procedure MakeJointPlan, a logic program searching
%  for a joint plan to execute a given program.
%

functor 

import

  LP at '../Utils/LP.ozf'
  Program at '../Program.ozf'
  SitCalc
  Exec
  ExView
  Step
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
          {Exec.holds E Cond}
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
              {Exec.holds E Cond}
              {Trans D1 E Dp Sp2}
              {Step.addtest Sp2 Cond Sp}
          []  {Exec.holds E neg(Cond)}
              {Trans D2 E Dp Sp2}
              {Step.addtest Sp2 neg(Cond) Sp}
          end
    []  wloop(Cond D1) then Sp2 in
          local D2 in
            {Exec.holds E Cond}
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
               choice  {Exec.holds E Cond} {Final D1 E}
               []   {Exec.holds E neg(Cond)} {Final D2 E}
               end
   []  wloop(Cond D1) then choice {Exec.holds E neg(Cond)} 
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
  %  Search for a join plan executing program D in the current situation.
  %  To do so, construct a closed PlanFront starting from now#D
  %
  proc {MakeJointPlan D JP} PFOut ExOut in
    {ClosePlanFront {PlanFront.init {Exec.init}#D} PFOut}
    JP = for collect:C E#_ in PFOut.closed do
              {C E}
            end
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
    Es#Ds = {PlanFront.select PFIn}
    Dp Sp Ep ExFunc
  in
    {Trans Ds Es Dp Sp}
    Ep = {Exec.insert Es Sp}
    % If no action was performed, then no other executions need
    % rolling forward and the expansion function is very simple.
    % Otherwise, we need to make all executions consistent with the step.
    if Sp.action == nil then
      ExFunc = proc {$ E#D Outs}
                 T EOut DOut
               in
                 if E == Es then DOut=Dp EOut=Ep
                 else DOut=D EOut=E end
                 if {IsFinal DOut EOut} then T = closed
                 else T = open end
                 Outs = [(E#D)#T]
               end
    else
      ExFunc = proc {$ E#D Outs}
                 Out2
               in
                 Out2 = for return:R default:unit
                        Agt in {SitCalc.actors Sp.action} do
                          if {Not {ExView.consistent Agt Ep E}} then RVal in
                            RVal = for collect:C
                                   E2#D2 in {ExpandWithStep E#D Ep Sp} do
                                     if {IsFinal D2 E2} then {C (E2#D2)#closed}
                                     else {C (E2#D2)#open} end
                                   end
                            {R RVal}
                          end
                        end
                 if Out2 == unit then
                   Outs = [(E#D)#(if {IsFinal D E} then closed else open end)]
                 else Outs = Out2 end
               end
    end
    PFOut = {PlanFront.expand PFIn ExFunc}
  end

  %
  %  Expand the given execution by a step compatible with the given step.
  %  The involves finding an action-bearing transition of E#D where the
  %  action matches S.action, inserting it onto E, ensuring that the
  %  result is consistent with Ep, and then determining all outcomes of
  %  that execution. Simple, huh? :-)
  %
  proc {ExpandWithStep E#D Ep Sp Exs}
    Dr Sr Er
  in
    {Trans D E Dr Sr}
    Er = {Exec.insert E Sr}
    if Sr.action == nil then
      Exs = {ExpandWithStep Er#Dr Ep Sp}
    else
      Sr.action = Sp.action
      for Agt in {SitCalc.actors Sp.action} do
        {ExView.consistent Agt Ep Er}
      end
      Exs = for collect:C Er2 in {Exec.outcomes Er} do
              if {IsFinal Dr Er2} then {C (Er2#Dr)#closed}
              else {C (Er2#Dr)#open} end
            end
    end
  end

  proc {Test}
    skip
  end

end
