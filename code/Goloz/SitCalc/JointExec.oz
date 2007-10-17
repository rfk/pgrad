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
%  is the label for event zero, a special outcome event triggering the
%  start of execution. 'finish' is the label of special action events
%  inserted to indicate that execution should terminate.
%
%  A branch of execution is a partial run of execution that selects one
%  outcome for each action performed.  It is identified by a sorted list
%  of outcome event IDs, highest ID first.  A branch Ns must satisfy the
%  following constraint:
%
%    all N < Ns.1:  N in NS  xor
%                   (exists N' in Ns: Conflicts(N N') v Preceeds(N N'))
%
%


functor

import

  IntMap at '../Utils/IntMap.ozf'
  SitCalc
 
  System

export

  Init
  Insert
  Assert
  Finish
  NextEvent
  Getobs

  WriteDotFile

define

  %
  %  Initialize a new (empty) joint execution.
  %  It will contain the single event 0, with label 'start'.
  %  'future' is a map from event ids to their details, indicating
  %  events that are yet to happen.  'past' is a list of events
  %  that have already occurred, most recently occurred event at head.
  %
  proc {Init J}
    StartEvent = out(obs: {SitCalc.newAgentMap} act: 0
                 enablers: nil outcomes:nil action:start)
  in
    for Agt in {Record.arity StartEvent.obs} do
      StartEvent.obs.Agt = start
    end
    J = je(future: {IntMap.append {IntMap.init} StartEvent}
           past: nil)
  end

  %
  %  Insert a new action into the execution.  S should be a record with
  %  feature 'action' containing the action to be added.  MustPrec should
  %  be a function taking as single argument an event ID, and returning true
  %  if that event must preceed the new event. Ns is the branch considered
  %  before the new action, and is used to determine the events that might
  %  preceed S.
  %
  %  The set of all possible outcomes of the action are automatically added,
  %  and returned in Outcomes.
  %
  proc {Insert JIn Ns S MustPrec JOut Outcomes}
    Ens = {FindEnablingEvents JIn S.action Ns MustPrec}
  in
    {InsertWithEnablers JIn Ns S Ens JOut Outcomes}
  end

  proc {InsertWithEnablers JIn Ns S Ens JOut Outcomes}
    Outs = {SitCalc.outcomes {BranchToRun JIn Ns} S}
    AId|OIds = {IntMap.nextAvailLabels JIn.future S|Outs}
    F0 F1 F2
  in
    F0 = JIn.future
    F1 = {IntMap.append F0 act(action: S.action enablers: Ens outcomes: OIds)}
    F2 = {InsertOutcomes AId F1 Outs OIds}
    JOut = {FixActionInvariants {Record.adjoinAt JIn future F2} AId}
    Outcomes = for collect:C I in OIds do
                 {C {BranchPush JOut I Ns}}
               end
  end

  %
  %  Utility function to insert a list of outcome events into the je.
  %
  proc {InsertOutcomes AId FIn Outs Ids FOut}
    case Outs of O|Os then F2 Is in
      Ids = _|Is
      F2 = {IntMap.append FIn out(obs: O.obs act: AId)}
      {InsertOutcomes AId F2 Os Is FOut}
    else FOut = FIn end
  end

  %
  %  Find the events that enable a new action event, by querying {MustPrec}.
  %  Ns is the branch after which the new event is being inserted, i.e.
  %  we assume that any events greater than Ns.1 conflict with the newly
  %  added event.
  %
  %  We special-case the handling of event zero so that it doesn't appear
  %  to the outside world via {MustPrec}
  %
  proc {FindEnablingEvents J Act Ns MustPrec Ens}
    EnsT = {FindEnablingEventsRec J Act Ns MustPrec}
  in
    if EnsT == nil then Ens = [0] else Ens = EnsT end
  end

  proc {FindEnablingEventsRec J Act Ns MustPrec Ens}
    case Ns of N|Nt then
      if N == 0 then
        Ens = nil
      elseif {Orderable J N Act} then
        if {MustPrec N} then
          % Orderable, and must preceed, so it's an enabler.
          % We can ignore the enablers of Ns.1 in further queries.
          Ens = N|_
          {FindEnablingEventsRec J Act Nt MustPrec Ens.2}
        else
          % Orderable, but may not preceed, so we get a choice point
          choice Ens = N|_
                 {FindEnablingEventsRec J Act Nt MustPrec Ens.2}
          []     {FindEnablingEventsRec J Act {BranchPop J Ns _} MustPrec Ens}
          end
        end
      else
        % Not orderable, so {MustPrec} must return false
        {MustPrec N} = false
        {FindEnablingEventsRec J Act {BranchPop J Ns _} MustPrec Ens}
      end
    else Ens = nil end
  end

  %
  %  Determine whether it's possible to order the action Act after
  %  event N.  For this to be true, event N must have an observation
  %  for the actor of Act.
  %
  proc {Orderable J N Act B}
    Data = {IntMap.get J.future N}
  in
    if Data.obs.{SitCalc.actor Act} == nil then B = false
    else B = true end
  end

  %
  %  Convert a branch into the unique run of execution determined
  %  by order of insertion.  The run is generated lazily.
  %
  fun lazy {BranchToRun J Ns}
    if Ns == [0] then
      now
    else H T in
      {BranchPop J Ns H T}
      ex({OutToStep J H} {BranchToRun J T})
    end
  end

  %
  %  Remove the latest event from the branch NsIn.
  %  Yields the event itself in N, and the preceeds branch
  %  in NsOut.
  %
  proc {BranchPop J NsIn N NsOut}
    OData = {IntMap.get J.future NsIn.1}
    AData = {IntMap.get J.future OData.act}
  in
    N = NsIn.1
    NsOut = {BranchPopAddEns J AData.enablers NsIn.2}
  end

  proc {BranchPopAddEns J Ens NsIn NsOut}
    case Ens of E|Es then Covered in
      Covered = for return:R default:false N in NsIn do
                  if {Preceeds J N E} then {R true} end
                end
      if Covered then
        {BranchPopAddEns J Es NsIn NsOut}
      else
        {BranchPopAddEns J Es {InsertInOrder E NsIn} NsOut}
      end
    else NsOut = NsIn end
  end

  proc {InsertInOrder I LIn LOut}
    if LIn == nil then LOut = [I]
    elseif I >= LIn.1 then LOut = I|LIn
    else LOut = LIn.1|{InsertInOrder I LIn.2} end
  end

  %
  %  Push a new event onto an existing branch.
  %
  proc {BranchPush J N NsIn NsOut}
    Keepers
  in
    Keepers = for collect:C N2 in NsIn do
                if {Not {Preceeds J N2 N}} then {C N2} end
              end
    NsOut = {InsertInOrder N Keepers}
  end

  %
  %  Construct a step object representing the outcome event O.
  %  This will contain only the 'action' and 'obs' features, since that's
  %  all a joint execution knows about.  This is also the only information
  %  needed to reason about what holds in a run.
  %
  proc {OutToStep J O S}
    OData = {IntMap.get J.future O}
    AData = {IntMap.get J.future OData.act}
  in
    S = step(action:AData.action obs:OData.obs)
  end

  %
  %  Utility procedurs for extracting different types of event.
  %    GetActions: get all ordinary action events (not finish actions)
  %    GetFinishes: get all finish events
  %
  proc {GetActions JIn Acts}
    Acts = {IntMap.allMatching JIn.future fun {$ I}
             D = {IntMap.get JIn.future I} in
             {Record.label D} == act andthen D.action \= finish
         end}
           end}
  end

  proc {GetFinishes: JIn Fs}
    Fs = {IntMap.allMatching JIn.future fun {$ I}
             D = {IntMap.get JIn.future I} in
             {Record.label D} == act andthen D.action == finish
         end}
  end

  %
  %  Check and correct any broken action invariants introduced by
  %  the addition of a new action event AId.
  %
  %  For now, this doesn't actually use the value of AId.  Figuring
  %  out how to use it to save time is an interesting topic for
  %  future research...
  %
  proc {FixActionInvariants JIn AId JOut}
    {FixInvariantActs JIn {GetActs JIn} JOut}
  end

  %
  %  Fix invariants for each action in the list Acts.
  %
  proc {FixInvariantActs JIn Acts JOut}
    case Acts of A|As then
      D = {IntMap.get JIn.future A} in
      if D.action == finish then {FixInvariantActs JIn As JOut}
      else
       Matches = {IndistinguishableSets JIn {SitCalc.actor D.action} D.enablers}
      in
       {FixInvariantMatches JIn As D Matches JOut}
      end
    else JIn = JOut end
  end

  %
  %  Ensure that for each entry Matches, there is an event corresponding
  %  to the action event A.
  %
  proc {FixInvariantMatches JIn Acts Act Matches JOut}
    case Matches of M|Ms then MAct in
      MAct = {IntMap.nextMatching JIn.future 0 fun {$ I} 
                        Data = {IntMap.get JIn.future I} in
                        if {Record.label Data} == act then
                          Data.enablers == M andthen Data.action == Act
                        else false end 
                     end}
      if MAct == nil then
        if {CannotInsertAfter JIn M} then fail
        else J2 in
          {InsertWithEnablers JIn M Act M J2 _}
          {FixInvariantMatches J2 Acts Act Ms JOut}
        end
      else
        {FixInvariantMatches JIn Acts Act Ms JOut}
      end
    else {FixInvariantActs JIn Acts JOut} end
  end

  proc {IndistinguishableSets J Agt Ens Matches}
    % TODO: JointExec.indistinguishableSets
    Matches = nil
  end

  % TODO: JointExec.cannotInsertAfter is currently too restrictive
  proc {CannotInsertAfter J Ns B}
    Fs = {GetFinishes J}
  in
    B = for return:R default:false N in Ns do
          for F in Fs do
            if {Preceeds N F} then {R true} end
          end
        end
  end

  %
  %  Assert that the given action is in the execution at event N.
  %  This is an analogue to {Insert} but instead of adding new actions,
  %  it verifies existing ones.
  %
  proc {Assert J Ns N S Preceeds Outcomes}
    Data = {IntMap.get J.future N}
    Outs
  in
    {System.printInfo "{Assert}\n"}
    Data.action = S.action
    Data.enablers = {FindEnablingEvents J S.action Ns Preceeds}
    Outs = {SitCalc.outcomes {BranchToRun J Ns}.2 S}
    {List.length Outs} = {List.length Data.outcomes}
    for O1 in Outs O2 in Data.outcomes do
      OData = {IntMap.get J.future O2} in
      OData.obs = O1.obs
    end
    Outcomes = for collect:C I in Data.outcomes do
                 {C {BranchPush J I Ns}}
               end
  end

  %
  %  Insert special 'finish' action to close the branch Ns
  %
  proc {Finish JIn Ns JOut}
    FEvent = act(action: finish enablers: Ns outcomes: nil)
  in
    JOut = {Record.adjoinAt JIn future {IntMap.append JIn.future FEvent}}
  end

  %
  %  Determine the next-oldest action event in the execution that
  %  could extend the run Ns. This will be nil if there is no such
  %  action, or an event identifier otherwise.
  %
  fun {NextEvent J Ns}
    {IntMap.nextMatching J.future Ns.1 fun {$ I} {Not {ConflictsB J I Ns}} end}
  end

  %
  %  Extract the observation data from last event in Ns into the record
  %  S.  The result is a record identical to S except that 'obs' is
  %  the observations in the outcome event, and 'seqn' is the event
  %  number.
  %
  proc {Getobs J Ns SIn SOut}
    Data = {IntMap.get J.future Ns.1}
  in
    SOut = {Record.adjoinList SIn [obs#Data.obs seqn#Ns.1]}
  end


  proc {NormalizeToAct J N1 N2 A1 A2}
    Data1 = {IntMap.get J.future N1}
    Data2 = {IntMap.get J.future N2}
  in
    case Data1 of out(...) then
      A1=Data1.act
      case Data2 of out(...) then A2=Data2.act
      else A1=N2 end
    else
      A1=N1
      case Data2 of out(...) then A2=Data2.act
      else A2=N2 end
    end
  end

  %
  %  Lazily generate a list of all observation events O for which
  %  {Preceeds O N} is true.  If N is also an observation event,
  %  it is included at the head of the list.
  %
  fun lazy {Preceeders J N}
    Data = {IntMap.get J.future N}
  in
    case Data of act(...) then {PreceedersA J [N]}
    else N|{PreceedersA J [Data.act]} end
  end
  fun lazy {PreceedersA J Ns}
    case Ns of N|NT then Data = {IntMap.get J.future N} in
      {PreceedersRec J NT Data.enablers}
    else nil end
  end
  fun lazy {PreceedersRec J Ns Ens}
    case Ens of E|Es then {List.append {Preceeders J E} {PreceedersRec J Ns Es}}
    else {PreceedersA J Ns} end
  end

  %
  %  Determine whether event N1 must preceed event N2.  This is
  %  so if it is enabler, or preceeds an enabler.  We can shortcut
  %  some cases since we know that larger IDs cannot preceed smaller
  %  IDs.  We also normalize things so that we're comparing two
  %  action events.
  %
  proc {Preceeds J N1 N2 B}
    if N1 >= N2 then B = false
    else A1 A2 in
      {NormalizeToAct J N1 N2 A1 A2}
      {PreceedsAct J A1 A2 B}
    end
  end
  proc {PreceedsAct J N1 N2 B}
    Data2 = {IntMap.get J.future N2} Enables
  in
    Enables = for return:R default:false E in Data2.enablers do
                 if {IntMap.get J.future E}.act == N1 then {R true} end
               end
    if Enables then B = true
    else B = for return:R default:false E in Data2.enablers do 
               if {PreceedsAct J N1 {IntMap.get J.future E}.act} then
                 {R true}
               end
             end
    end
  end

  %
  %  Determine whether events N1 and N2 are in conflict.
  %  This is true if they are alternate outcomes of the same action,
  %  or if are preceeded by conflicting actions.
  %
  proc {Conflicts J N1 N2 B}
    if N1 == N2 then B = false
    else
      B = for return:R default:false P1 in {Preceeders J N1} do
            for P2 in {Preceeders J N2} do
              if P1 \= P2 then A1 A2 in
                A1 = {IntMap.get J.future P1}.act
                A2 = {IntMap.get J.future P2}.act
                if A1 == A2 then {R true} end
              end
            end
          end
    end
  end

  proc {WalkList L}
    case L of _|Tail then {WalkList Tail} else skip end
  end

  %
  %  Determine whether event I conflicts with any events in branch Ns.
  %
  proc {ConflictsB J I Ns B}
    case Ns of N|NT then
      if {Conflicts J I N} then
        B = true
      else
        B = {ConflictsB J I NT}
      end
    else B = false end
  end

  %
  %  Write a Graphviz dot-file representing the joint execution.
  %  File can be any object supporting the 'write' method.
  %
  proc {WriteDotFile J File}
    {File write(vs: "digraph G {\n")}
    {IntMap.forEach J.future
       proc {$ N}
          Data = {IntMap.get J.future N}
       in
         case Data of act(...) then
           {File write(vs: "n"#N#" [shape=ellipse,label=\""#{Value.toVirtualString Data.action ~1 ~1}#"\"];\n")}
           for E in Data.enablers do
             {File write(vs: "n"#E#" -> n"#N#";\n")}
           end
           for O in Data.outcomes do
             {File write(vs: "n"#N#" -> n"#O#";\n")}
           end
         else
           {File write(vs: "n"#N#" [shape=box,label=\""#{OutcomeLabel Data}#"\"];\n")}
         end
       end
    }
    {File write(vs: "}\n")}
  end

  proc {OutcomeLabel OData Lbl}
    Lbls
  in
    Lbls = for collect:C Agt in {Record.arity OData.obs} do
             {C Agt#": "#{Value.toVirtualString OData.obs.Agt ~1 ~1}#"\\n"}
           end
    Lbl = {List.toTuple '#' Lbls}
  end

end
