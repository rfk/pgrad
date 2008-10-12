%
%  Planner.oz:  construct a JointExec for a given program.
%
%  The planning process proceeds by maintaining a list of open branches,
%  selecting and extending a branch repeatedly until they are all closed.
%
%  A branch is a tuple D#R#N where D is the program remaining to be executed,
%  R is the run of execution so far, and N is the corresponding branch in
%  the joint execution.
%

functor 

import

  MIndiGolog
  JointExec
  Domain
  Sitcalc
  LP

  System
  Search

export

  Plan

define

  %
  %  Search for a joint execution of program D in the current situation.
  %  To do so, we start with a single branch containing the entire program,
  %  an empty run and empty JointExec branch.
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
    BClosed BRest
  in
    {System.showInfo "{MakePlan}"}
    {System.print {List.length Branches}}
    {System.printInfo " branches to process\n"}
    {FindOpenBranch JIn Branches BClosed BRest}
    {System.print {List.length BClosed}} {System.showInfo " closed"}
    case BRest of (D#R#N)|Bs then Dp Rp S J2 OutNs OutBs in
       {System.showInfo "trying to trans1"}
       {FindTrans1 D R Bs Dp Rp S}
       {System.printInfo "...found: "}
       {System.show S.action}
       OutNs = {JointExec.insert JIn N S {MkPrecFunc S Rp} J2}
       {System.showInfo "...inserted"}
       OutBs = for collect:C N2 in OutNs do
                     {C Dp#ex({JointExec.getout J2 N2 S} Rp)#N2}
                  end
       {MakePlan J2 {List.append BClosed {List.append OutBs Bs}} JOut}
    else {System.showInfo "all done!"} JOut = JIn end
  end

  %
  %  Find the first open branch in the given list.
  %  Each branch is rolled forward to handle any existing events
  %  before it is checked.  The list BClosed will be the closed
  %  branches at the head of Branches, while BRest is the rest of the
  %  list.  BRest.1 will be the first open branch.
  %
  proc {FindOpenBranch J Branches BClosed BRest}
    case Branches of (D1#R1#N1)|Bs then D R N NewBs in
        (D#R#N)|NewBs = {HandleExistingEvents J D1#R1#N1}
        if {MIndiGolog.isFinal D R} then
          BClosed = (D#R#N)|_
          {FindOpenBranch J {List.append NewBs Bs} BClosed.2 BRest}
        else
          BClosed = nil BRest = (D#R#N)|{List.append NewBs Bs}
        end
    else BClosed = nil BRest = nil end
  end


  %
  %  Find a step of execution for the given D#R.  This wraps
  %  MIndiGolog.trans1 to return the potential solutions in order
  %  of 'most promising' to 'least promising', according to how
  %  much concurrency is present.
  %
  proc {FindTrans1 D R Bs Dp Rp S}
    Searcher SearchProc
  in
    proc {SearchProc Q} Dp Rp S in
      {MIndiGolog.trans1 D R Dp Rp S}
      Q = Dp#Rp#S
    end
    Searcher = {New Search.object script(SearchProc)}
    Dp#Rp#S = {LP.yieldOrdered Searcher CompareTrans1}
  end

  %
  %  Determine whether the first transition is better than the
  %  second transition.  This is determined based on how many
  %  actions the latest step can be performed concurrently with.
  %
  proc {CompareTrans1 _#Rp1#S1 _#Rp2#S2 B}
    N1 = {NumConc Rp1 S1}
    N2 = {NumConc Rp2 S2}
  in
    if N1 > N2 then B=true
    elseif N1 < N2 then B=false
    else B=({RunLength Rp1} < {RunLength Rp2}) end
  end

  proc {NumConc R S N}
    case R of ex(S2 R2) then
      if S2.action == nil then N = {NumConc R2 S}
      elseif {MustPrec S2 S} then N = 0
      else N = 1 + {NumConc R2 S} end
    else N = 0 end
  end

  proc {RunLength R N}
    case R of ex(_ R2) then N = 1 + {RunLength R2}
    else N = 0 end
  end


  %
  %  Create a function that will determine ordering when inserting
  %  into a joint exec.  This is basically a closure around the function
  %  {MustPrec} to transform the event into a proper step record based
  %  on the current run.
  %
  proc {MkPrecFunc S R F}
    proc {F N B}
      S2 = {GetStepFromRun N R}
    in
      if S2 == nil then B = false
      else B = {MustPrec S2 S} end
    end
  end

  %
  %  Convert an JointExec event id into a step object from the given
  %  run.  If a corresponding step cannot be found, returns nil.
  %
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
  proc {MustPrec S1 S2 B}
    if {Not {Domain.indep S1.action S2.action}} then B = true
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
    Ne = {JointExec.nextEvent J N}
  in
    if Ne == nil then
      Branches=[D#R#N]
    else OutNs Dp Rp S in
      {MIndiGolog.trans1 D R Dp Rp S}
      OutNs = {JointExec.assert J N Ne S {MkPrecFunc S Rp}}
      Branches=for append:Acc OutN in OutNs do
                 S2 = {JointExec.getout J OutN S} in
                 {Acc {HandleExistingEvents J Dp#ex(S2 Rp)#OutN}}
               end
    end
  end

end

