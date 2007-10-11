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

export

  Plan

define

  %
  %  Search for a joint execution of program D in the current situation.
  %  To do so, we start with a single branch containing the entire program,
  %  an empty run and a most-recent-event of zero.
  %
  proc {Plan D J}
    {MakePlan {JointExec.init} [D#now#0] J}
  end

  %
  %  Construct a joint execution, one step at a time, one branch at a time.
  %  JIn is the joint plan constructed so far.
  %  Branches is a list of D#R#N tuples that are still to be processed.
  %
  proc {MakePlan JIn Branches JOut}
    case Branches of (D1#R1#N1)|Bs then
      (D#R#N)|NewBs = {HandleExistingEvents JIn D1#R1#N1} in
      choice J2 in
           {MIndiGolog.final D R}
           J2 = {JointExec.finish JIn N}
           {MakePlan J2 {List.append NewBs Bs} JOut}
      [] Dp Rp S J2 OutSs OutNs OutBs in
           {MIndiGolog.trans1 D R Dp Rp S}
           OutNs = {JointExec.insert JIn S {MkPreceedsF S Rp} J2}
           OutBs = for collect:C N2 in OutNs do
                         {C Dp#ex({JointExec.getobs J2 N2 S} Rp)#N2}
                      end
           {MakePlan J2 {List.append OutBs {List.append NewBs Bs}} JOut}
      end
    else JOut = JIn end
  end

  %
  %  Create a function that will determine ordering when inserting
  %  into a joint plan.  This is basically a closure around  the function
  %  {Preceeds} to include the current step and run of execution.
  %
  fun {MkPreceedsF S R}
    fun {$ S1} {Preceeds S1 S R} end
  end

  %
  %  Determine whether step S1 must preceed step S2 in the joint plan.
  %  This must be true if {Ordered S1 S2 R}, and can be true only if
  %  {Orderable S1 S2}.  If they are orderable but not neessarily ordered,
  %  this procedure can return either true or false, so a choicepoint is 
  %  created.
  %
  proc {Preceeds S1 S2 R B}
    if {Orderable S1 S2} then
      if {Ordered S1 S2 R} then B=true
      else choice B=true [] B=false end end
    else
      if {Ordered S1 S2 R} then fail
      else B=false end
    end
  end

  proc {Orderable S1 S2 B}
    % TODO: Planner.orderable
    B = true
  end

  proc {Ordered S1 S2 R B}
    % TODO: Planner.ordered
    B = false
  end

  %
  %  Transition the program D so that any events inserted after N are
  %  accounted for.  This ensures that its execution is compatible with
  %  those of existing branches.  Since this may in itself create
  %  additional branch points if steps with multiple alternatives have
  %  been added, the result is a list of branches.
  %
  proc {HandleExistingEvents J D#R#N Branches}
    N2 = {JointExec.nextEvent J N}
  in
    if N2 == nil then
      Branches=[D#R#N]
    else OutNs in
      {MIndiGolog.trans1 D R Dp Rp S}
      OutNs = {JointExec.assert J N2 S {MkPreceedsF S Rp}}
      Branches=for append:Acc OutN in OutNs do
                 S2 = {JointExec.getobs J OutN S} in
                 {Acc {HandleExistingEvents J Dp#ex(S2 Rp)#N2}}
               end
    end
  end

end

