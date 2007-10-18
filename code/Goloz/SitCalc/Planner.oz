%
%  Planner.oz:  construct a JointExec for a given program.
%
%  The planning process proceeds by maintaining a list of open branches,
%  selecting and extending a branch repeatedly until they are all closed.
%
%  A branch is a tuple D#R#N where D is the program remaining to be executed,
%  R is the run of execution so far, and N is the most recently added event
%  in the joint execution.
%

functor 

import

  MIndiGolog
  JointExec
  SitCalc

  System
  Search
  Explorer

export

  Plan
  Test

define

  %
  %  Search for a joint execution of program D in the current situation.
  %  To do so, we start with a single branch containing the entire program,
  %  an empty run and empty branch.
  %
  proc {Plan D J}
    {MakePlan {JointExec.init} [D#now#nil] J}
  end

  %
  %  Construct a joint execution, one step at a time, one branch at a time.
  %  JIn is the joint exec constructed so far.
  %  Branches is a list of D#R#N tuples that are still to be processed.
  %
  proc {MakePlan JIn Branches JOut}
    {System.printInfo "{MakePlan}\n"}
    {System.print {List.length Branches}}
    {System.printInfo " branches to go\n"}
    case Branches of (D1#R1#N1)|Bs then D R N NewBs in
      (D#R#N)|NewBs = {HandleExistingEvents JIn D1#R1#N1}
      {System.printInfo "handled\n"}
      choice J2 in
           {System.showInfo "trying to finish..."}
           {MIndiGolog.final D R}
           J2 = {JointExec.finish JIn N}
           {System.printInfo "branch closed!\n"}
           {MakePlan J2 {List.append NewBs Bs} JOut}
      [] Dp Rp S J2 OutNs OutBs in
           {System.showInfo "trying to trans1..."}
           {MIndiGolog.trans1 D R Dp Rp S}
           {System.showInfo "...found"}
           OutNs = {JointExec.insert JIn N S {MkPreceedsF S Rp} J2}
           {System.showInfo "...inserted"}
           OutBs = for collect:C N2 in OutNs do
                         {C Dp#ex({JointExec.getobs J2 N2 S} Rp)#N2}
                      end
           {System.showInfo "...ok, transition made!"}
           {MakePlan J2 {List.append OutBs {List.append NewBs Bs}} JOut}
      end
    else JOut = JIn end
  end

  %
  %  Create a function that will determine ordering when inserting
  %  into a joint exec.  This is basically a closure around the function
  %  {Preceeds} to transform the event into a proper step record based
  %  on the current run.
  %
  proc {MkPreceedsF S R F}
    proc {F N B}
      S2 = {GetStepFromRun N R}
    in
      if S2 == nil then B = false
      else B = {Preceeds S2 S} end
    end
  end

  proc {GetStepFromRun N R S}
    case R of ex(S2 R2) then
      if S2.seqn == N then S = S2
      else S = {GetStepFromRun N R2} end
    else S = nil end
  end

  %
  %  Determine whether step S1 must preceed step S2 in the joint exec.
  %  This is true if:
  %     - their actions are not independent
  %     - S1.thred is a prefix of S2.thred, or vice-versa
  %     - S2.action doesn't falsify S1.test (TODO)
  %
  proc {Preceeds S1 S2 B}
    if {Not {SitCalc.independentActs S1.action S2.action}} then B = true
    elseif {List.isPrefix S1.thred S2.thred} then B = true
    elseif {List.isPrefix S2.thred S1.thred} then B = true
    else B = false end
  end

  %
  %  Transition the program D so that any events inserted after N are
  %  accounted for.  This ensures that its execution is compatible with
  %  those of existing branches.  Since this may in itself create
  %  additional branch points if steps with multiple outcomes have
  %  been added, the result is a list of branches.
  %
  proc {HandleExistingEvents J D#R#N Branches}
    N2 = {JointExec.nextEvent J N}
  in
    {System.printInfo "HandleExistingEvents\n"}
    if N2 == nil then
      {System.printInfo "- clear\n"}
      Branches=[D#R#N]
    else OutNs Dp Rp S in
      {System.printInfo "- adding\n"}
      {System.print N#N2}
      {System.printInfo "\n"}
      {System.print J}
      {System.printInfo "\n"}
      {MIndiGolog.trans1 D R Dp Rp S}
      OutNs = {JointExec.assert J N N2 S {MkPreceedsF S Rp}}
      Branches=for append:Acc OutN in OutNs do
                 S2 = {JointExec.getobs J OutN S} in
                 {Acc {HandleExistingEvents J Dp#ex(S2 Rp)#N2}}
               end
    end
  end

  proc {Test}
    Plans = [acquire(thomas lettuce(1))
             seq(acquire(thomas lettuce(1)) acquire(richard lettuce(1)))
             seq(check_for(thomas lettuce) acquire(richard lettuce(1)))
             seq(check_for(thomas lettuce) acquire(thomas lettuce(1)))
            ]
    Sols = [true false false true]
  in
    for P in Plans S in Sols do Sol in
      Sol = {Search.base.one proc {$ Q} {Plan P Q} end}
      if S \= (Sol \= nil) then raise plan(P Sol\=nil) end end
      {System.showInfo " "}
      {System.showInfo " "}
      {System.showInfo " "}
    end
  end

end

