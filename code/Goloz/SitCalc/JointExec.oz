%
%  JointExec.oz
%
%  Implements a joint execution, a prime event structure over actions
%  and their outcomes that can be performed in a reactive manner by 
%  a team of agents.
%
%  Each event in the execution is uniquely identified by an integer,
%  which is its order of insertion.  Events are separated into two types:
%      * action events, representing actions performed by the agents
%      * outcome events, representing observations made by the agents
%        as a result of an action being performed
%
%  Only action events can be added to the execution explicitly - outcome
%  events are automatically added for every action.
%
%  There are two special events labels 'start' and 'finish'. 'start'
%  is the label for event zero, a special outcome event triggerig the
%  start of execution. 'finish' is the label of pseudo action events
%  inserted to indicate that execution has terminated.
%
%  A branch of execution (selecting one outcome from each action) is
%  uniquely identified using a sorted list of outcome events Ns, highest id 
%  first.  It must satisfy the following:
%
%    all N < Ns.1:  N in NS  xor
%                   (exists N' in Ns: Conflicts(N N')  v  Preceeds(N N'))
%  
%


functor

import

  IntMap at '../Utils/IntMap.ozf'
  SitCalc

export

  Init
  Insert
  Assert
  Finish
  NextEvent
  Getobs

define

  %
  %  Initialize a new (empty) joint execution.
  %  It will contain the single event 0, with label 'start'.
  %  'future' is a map from event ids to theri details, indicating
  %  events that are yet to happen.  'past' is a list of events
  %  that have already occurred, most recently occurred event at head.
  %
  proc {Init J}
    J = je(
            future: {IntMap.append {IntMap.init} out(start)}
            past: nil
          )
  end

  %
  %  Insert a new action into the execution.  S should be a record with
  %  with feature 'action' containing the action to be added.  Preceeds
  %  should be a function taking as single argument an event ID, and returning
  %  true if that event must preceed the new event. Ns is the branch considered
  %  before the new action, and is used to determine the events that might
  %  preceed S.
  %
  %  The set of all possible outcomes of the action and automatically added,
  %  and returned in Outcomes.
  %
  proc {Insert JIn Ns S Preceeds JOut Outcomes}
    Ens = {FindEnablingEvents JIn Ns Preceeds}
    Outs = {SitCalc.outcomes {BranchToRun J Ns} S}
    AId|OIds = {IntMap.newLabels JIn.future S|Outs}
    F0 F1 F2 F3
  in
    F0 = JIn.future
    F1 = {IntMap.append F0 act(action: S.action enablers: Ens outcomes: OIds)}
    F2 = {InsertOutcomes AId F1 Outs OIds}
    F3 = {FixActionInvariants F2 AId}
    JOut = {Record.adjoinAt JIn future F2}
    Outcomes = for collect:C I in OIds do
                 {C {BranchPush JOut I Ns}}
               end
  end

  proc {FindEnablingEvents J Ns Preceeds}
    % TODO: JointExec.findEnablingEvents
    skip
  end

  fun lazy {BranchToRun J Ns}
    if Ns == [0] then
      now
    else H T in
      {BranchPop J Ns H T}
      ex({OutToStep J H} {BranchToRun J T})
    end
  end

  proc {BranchPop J NsIn N NsOut}
    % TODO: JointExec.branchPop
    N = NsIn.1
    NsOut = NsIn
  end

  proc {BranchPush J NsIn N NsOut}
    % TODO: JointExec.branchPop
    N = NsIn.1
    NsOut = NsIn
  end

  proc {OutToStep J O S}
    OData = {IntMap.get J.future O}
    AData = {IntMap.get J.future OData.act}
  in
    S = step(action:AData.action obs:OData.obs)
  end

  proc {InsertOutcomes AId FIn Outs Ids FOut}
    case Outs of O|Os then F2 in
      Ids = I|Is
      F2 = {IntMap.append FIn out(obs: O.obs act: AId)}
      {InsertOutcomes AId F2 Os Is FOut}
    else FOut = FIn end
  end

  proc {FixActionInvariants FIn AId FOut}
    % TODO: JointExec.fixActionInvariants
    skip
  end

  %
  %  Assert that the given action is in the execution at event N.
  %  This is an analogue to {Insert} but instead of adding new actions,
  %  it verifies existing ones.
  %
  proc {Assert J Ns S Preceeds Outcomes}
    Data = {IntMap.get J.future Ns.1}
    Ens Outs
  in
    Data.action = S.action
    Ens = {FindEnablingEvents J {BranchPop Ns _} Preceeds}
    Data.enablers = Ens
    Outs = {SitCalc.outcomes {BranchToRun J Ns}.2 S}
    Data.outcomes = Outs
    Outcomes = for collect:C I in Outs do
                 {C {BranchPush J I Ns}}
               end
  end

  %
  %  Insert special 'finish' action in the run ending at N.
  %
  proc {Finish JIn N JOut}
    % TODO: JointExec.finish ... do we even want to do it this way?
    JOut = JIn
  end

  %
  %  Determine the next-oldest action event in the execution that
  %  could extend the run Ns. This will be nil if there is no such
  %  action, or an event identifier otherwise.
  %
  fun {NextEvent J Ns}
    {IntMap.nextMatching J.future N.1 fun {$ I} {Not {ConflictsB J I Ns}}}
  end

  %
  %  Extract the observation data from last event in Ns into the record term
  %  S.  The result is a record identical to S except that 'obs' is
  %  the observations in the outcome event, and 'seqn' is the event
  %  number.
  %
  proc {Getobs J Ns SIn SOut}
    Data = {IntMap.get J.future Ns.1}
  in
    SOut = {Record.adjoinList SIn [obs#Data.obs seqn#Ns.1]}
  end


  proc {Preceeds J I1 I2 B}
    % TODO: JointExec.preceeds
    skip
  end

  proc {Conflicts J I1 I2 B}
    % TODO: JointExec.conflicts
    skip
  end

  proc {ConflictsB J I Ns B}
    case Ns of N|NT then
      if {Conflicts J I N} then
        B = true
      else
        B = {ConflictsB J I NT}
      end
    else B = false end
  end

end
