%
%  Planner.oz:  construct a JointPlan for a given program.
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

  SitCalc
  MIndiGolog
  Step
  JointPlan

export

  Plan

define

  %
  %  Search for a joint plan executing program D in the current situation.
  %  To do so, we start with a single branch containing the entire program,
  %  an empty run and a most-recent-event of zero.
  %
  proc {Plan D JP}
    {MakePlan {JointPlan.init} [D#now#0] JP}
  end

  %
  %  Construct a joint plan, one step at a time, one branch at a time.
  %  JPIn is the joint plan constructed so far.
  %  Branches is a list of D#R#N tuples that are still to be processed.
  %
  proc {MakePlan JPIn Branches JPOut}
    case Branches of (D1#R1#N1)|Bs then
      (D#R#N)|NewBs = {HandleExistingEvents JPIn D1#M1#N1} in
      choice JP2 in
           {Final D R}
           JP2 = {JointPlan.finish JPIn N}
           {MakePlan JP2 {List.append NewBs Bs} JPOut}
      [] Dp Rp S OutEs OutBs in
           {Trans1 D R Dp Rp S}
           OutEs = {JointPlan.insert JPIn S {MkPreceedsF S R} JP2}
           OutBs = for collect:C N2 in OutEs do
                       {C Dp#ex({JointPlan.getEvent JP2 N2} Rp)#N2}
                      end
           {MakePlan JP2 {List.append OutBs {List.append NewBs Bs}} JPOut}
      end
    else JPOut = JPIn end
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
  proc {HandleExistingEvents JP D#R#N Branches}
    N2s = {JointPlan.nextEvents JP N}
  in
    if N2s == nil then
      Branches=[D#R#N]
    else
      Branches=for append:A N2 in N2s do Dp Rp S in
                 {Trans1 D R Dp Rp S}
                 {JointPlan.getEvent JP N2 S}
                 {JointPlan.assert JP N2 S {MkPreceedsF S Rp}}
                 {A {HandleExistingEvents JP D2#ex(S Rp)#N2}}
               end
      
    end
  end

end

