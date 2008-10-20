%
%  Planner.oz:  construct a JointExec for a given program.
%
%  Copyright 2008, Ryan Kelly
%
%  The planning process proceeds by maintaining a list of open leaves,
%  selecting and extending a leaf repeatedly until they are all closed.
%
%  A leaf is a tuple D#H#L where D is the program remaining to be executed,
%  H is the execution history so far, and L is the corresponding leaf in
%  the joint execution.
%

functor 

import

  MIndiGolog
  JointExec
  Domain
  LP

  System
  Search

export

  Plan

define

  %
  %  Search for a joint execution of program D in the current situation.
  %  To do so, we start with a single leaf containing the entire program,
  %  and an empty history.
  %
  proc {Plan D J}
    {MakePlan {JointExec.init} [D#now#nil] J}
  end

  %
  %  Construct a joint execution, one step at a time, one leaf at a time.
  %  JIn is the joint exec constructed so far.
  %  Leaves is a list of D#H#L tuples that are still to be processed.
  %
  proc {MakePlan JIn Leaves JOut}
    LCls LRest
  in
    {System.showInfo "{MakePlan}"}
    {System.print {List.length Leaves}}
    {System.printInfo " leaves to process\n"}
    {FindOpenLeaf JIn Leaves LCls LRest}
    {System.print {List.length LCls}} {System.showInfo " closed"}
    case LRest of (D#H#L)|Ls then Dp Hp S J2 OutNs OutLs in
       {System.showInfo "trying to trans1"}
       {FindTrans1 D H Ls Dp Hp S}
       {System.printInfo "...found: "}
       {System.show S.action}
       OutNs = {JointExec.insert JIn L S {MkPrecFunc S Hp} J2}
       {System.showInfo "...inserted"}
       OutLs = for collect:C N2 in OutNs do
                     {C Dp#ex({JointExec.getout J2 N2 S} Hp)#N2}
                  end
       {MakePlan J2 {List.append LCls {List.append OutLs Ls}} JOut}
    else {System.showInfo "all done!"} JOut = JIn end
  end

  %
  %  Find the first open leaf in the given list.
  %  Each leaf is rolled forward to handle any existing events
  %  before it is checked.  The list LCls will be the closed
  %  leaves at the head of Leaves, while LRest is the rest of the
  %  list.  LRest.1 will be the first open leaf.
  %
  proc {FindOpenLeaf J Leaves LCls LRest}
    case Leaves of (D1#H1#L1)|Ls then D H L NewLs in
        (D#H#L)|NewLs = {HandleExistingEvents J D1#H1#L1}
        if {MIndiGolog.isFinal D H} then
          LCls = (D#H#L)|_
          {FindOpenLeaf J {List.append NewLs Ls} LCls.2 LRest}
        else
          LCls = nil LRest = (D#H#L)|{List.append NewLs Ls}
        end
    else LCls = nil LRest = nil end
  end


  %
  %  Find a step of execution for the given D#H.  This wraps
  %  MIndiGolog.trans1 to return the potential solutions in order
  %  of 'most promising' to 'least promising', according to how
  %  much concurrency is present.
  %
  proc {FindTrans1 D H Ls Dp Hp S}
    Searcher SearchProc
  in
    proc {SearchProc Q} Dp Hp S in
      {MIndiGolog.trans1 D H Dp Hp S}
      Q = Dp#Hp#S
    end
    Searcher = {New Search.object script(SearchProc)}
    Dp#Hp#S = {LP.yieldOrdered Searcher CompareTrans1}
  end

  %
  %  Determine whether the first transition is better than the
  %  second transition.  This is determined based on how many
  %  actions the latest step can be performed concurrently with.
  %
  proc {CompareTrans1 _#Hp1#S1 _#Hp2#S2 B}
    N1 = {NumConc Hp1 S1}
    N2 = {NumConc Hp2 S2}
  in
    if N1 > N2 then B=true
    elseif N1 < N2 then B=false
    else B=({RunLength Hp1} < {RunLength Hp2}) end
  end

  proc {NumConc H S N}
    case H of ex(S2 H2) then
      if S2.action == nil then N = {NumConc H2 S}
      elseif {MustPrec S2 S} then N = 0
      else N = 1 + {NumConc H2 S} end
    else N = 0 end
  end

  proc {RunLength H N}
    case H of ex(_ H2) then N = 1 + {RunLength H2}
    else N = 0 end
  end


  %
  %  Create a function that will determine ordering when inserting
  %  into a joint exec.  This is basically a closure around the function
  %  {MustPrec} to transform the event into a proper step record based
  %  on the current history.
  %
  proc {MkPrecFunc S H F}
    proc {F N B}
      S2 = {GetStepFromRun N H}
    in
      if S2 == nil then B = false
      else B = {MustPrec S2 S} end
    end
  end

  %
  %  Convert an JointExec event id into a step object from the given
  %  history run.  If a corresponding step cannot be found, returns nil.
  %
  proc {GetStepFromRun N H S}
    case H of ex(S2 H2) then
      if S2.seqn == N then S = S2
      else S = {GetStepFromRun N H2} end
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
  %  those of existing leaves.  Since this may in itself create
  %  additional branch points if steps with multiple outcomes have
  %  been added, the result is a list of leaves.
  %
  proc {HandleExistingEvents J D#H#L Leaves}
    Ne = {JointExec.nextEvent J L}
  in
    if Ne == nil then
      Leaves=[D#H#L]
    else OutLs Dp Hp S in
      {MIndiGolog.trans1 D H Dp Hp S}
      OutLs = {JointExec.assert J L Ne S {MkPrecFunc S Hp}}
      Leaves=for append:Acc OutL in OutLs do
                 S2 = {JointExec.getout J OutL S} in
                 {Acc {HandleExistingEvents J Dp#ex(S2 Hp)#OutL}}
               end
    end
  end

end

