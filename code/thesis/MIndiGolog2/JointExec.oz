%
%  JointExec.oz:  joint executions as an abstract data type
%
%  Copyright 2008, Ryan Kelly
%
%  This file implements joint executions, a prime event structure over actions
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
%  A special action labelled 'finish' is used to indicate that a branch
%  of execution has completed execution, and no more actions should be
%  added to it.
%


functor

import

  IntMap
  Sitcalc
  LP
 
  Search

export

  Init
  Insert
  Assert
  Finish
  NextEvent
  Getout

  WriteDotFile

define

  %
  %  Initialize a new (empty) joint execution.
  %
  proc {Init J}
    J = {IntMap.init}
  end

  %  Insert a new action into the execution.  S should be a record with
  %  feature 'action' containing the action to be added.  MustPrec should
  %  be a function taking as single argument an event ID, and returning true
  %  if that event must preceed the new event. Lf is the leaf on which
  %  the action is being inserted, and is used to determine the events
  %  that might preceed S.
  %
  %  The set of all possible outcomes of the action are automatically added,
  %  with the corresponding expanded leaves being returned in Outcomes.
  %
  proc {Insert JIn Lf S MustPrec JOut Outcomes}
    Ens = {FilterEnablers JIn {FindEnablingEvents JIn S.action Lf MustPrec}}
  in
    {InsertWithEnablers JIn Lf S Ens JOut Outcomes}
  end

  proc {InsertWithEnablers JIn Lf S Ens JOut Outcomes}
    Outs = {Sitcalc.outcomes S}
    AId|OIds = {IntMap.nextAvailLabels JIn S|Outs}
    J1 J2
  in
    J1 = {IntMap.append JIn act(action:S.action enablers:Ens outcomes:OIds)}
    J2 = {InsertOutcomes AId J1 Outs OIds}
    JOut = {FixFeasibility J2 AId}
    Outcomes = for collect:C I in OIds do
                 {C {BranchPush JOut I Lf}}
               end
  end

  %
  %  Utility function to insert a list of outcome events into the joint exec.
  %
  proc {InsertOutcomes AId JIn Outs Ids JOut}
    case Outs of O|Os then J2 Is in
      Ids = _|Is
      J2 = {IntMap.append JIn out(out: O.out act: AId)}
      {InsertOutcomes AId J2 Os Is JOut}
    else JOut = JIn end
  end

  %
  %  Find the events that enable a new action event, by querying {MustPrec}.
  %  Lf is the leaf on which the new event is being inserted, i.e.
  %  we assume that any events greater than Lf.1 conflict with the newly
  %  added event.
  %
  %  This procedure is nondeterministic, as many events may be able to
  %  enable to new event, but not required to.
  %
  proc {FindEnablingEvents J Act Ns MustPrec Ens}
    case Ns of N|Nt then
      if {Orderable J N Act} then
        if {MustPrec N} then
          % Orderable, and must preceed, so it's an enabler.
          Ens = N|_
          {FindEnablingEvents J Act Nt MustPrec Ens.2}
        else
          % Orderable, but not required to preceed, so we get a choice point
          choice {FindEnablingEvents J Act {BranchPop J Ns _} MustPrec Ens}
          []     Ens = N|_
                 {FindEnablingEvents J Act Nt MustPrec Ens.2}
          end
        end
      else
        % Not orderable, so {MustPrec} must return false
        {MustPrec N} = false
        {FindEnablingEvents J Act {BranchPop J Ns _} MustPrec Ens}
      end
    else Ens = nil end
  end

  %  Filter redundant information out of a list of enabling events - 
  %  basically make sure they they are all unordered.
  %
  proc {FilterEnablers J EnsIn EnsOut}
    EnsOut = for collect:C N1 in EnsIn do
              if for return:R default:false N2 in EnsIn do
                   if {Preceeds J N1 N2} then {R true} end
                 end
              then skip else {C N1} end
            end
  end

  %
  %  Determine whether it's possible to order the action Act after
  %  event N.  For this to be true, event N must have an observation
  %  for the actor of Act.
  %
  proc {Orderable J N Act B}
    Data = {IntMap.get J N}
  in
    if {Record.label Data} \= out then B = false
    elseif Data.out.{Sitcalc.actor Act} == nil then B = false
    else B = true end
  end

  %
  %  Remove the latest event from the branch NsIn.
  %  Outputs the event itself in N, and the preceeding branch
  %  in NsOut.
  %
  proc {BranchPop J NsIn N NsOut}
    OData = {IntMap.get J NsIn.1}
    AData = {IntMap.get J OData.act}
  in
    N = NsIn.1
    NsOut = {BranchPopAddEns J AData.enablers NsIn.2}
  end

  %
  %  Utility function to add the necessary enablers of an event
  %  into a branch it has been popped from.
  %
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

  %
  %  Utility function for inserting into a sorted list
  %
  proc {InsertInOrder I LIn LOut}
    if LIn == nil then LOut = [I]
    elseif I >= LIn.1 then LOut = I|LIn
    else LOut = LIn.1|{InsertInOrder I LIn.2} end
  end

  %
  %  Push a new event onto an existing branch.
  %
  proc {BranchPush J N NsIn NsOut}
    Keepers = for collect:C N2 in NsIn do
                if {Not {Preceeds J N2 N}} then {C N2} end
              end
  in
    NsOut = {InsertInOrder N Keepers}
  end

  %  Determine whether B1 is "smaller" than branch B2. 
  %  This means that everything in B1 is either also in B2,
  %  or preceeds something in B2.
  %
  proc {BranchIsSmaller J B1 B2 B}
    B = for return:R default:true N1 in B1 do Covered in
          Covered = for return:R2 default:false N2 in B2 do
                      if {Preceeds J N1 N2} then {R2 true} end
                      if N1 == N2 then {R2 true} end
                    end
          if {Not Covered} then {R false} end
        end
  end

  %  Reduce a set of enabling branches to the minimal set possible.
  %  Any entries in Bs that are larger than another entry are
  %  removed.
  %
  proc {MinimizeBranchSet J Bs MinBs}
    {MinimizeBranchSetRec J Bs nil MinBs}
  end

  proc {MinimizeBranchSetRec J Bs Acc MinBs}
    case Bs of B|Bs2 then Covered in
      Covered = for return:R default:false A in Acc do
                  if {BranchIsSmaller J A B} then {R true} end
                end
      if Covered then {MinimizeBranchSetRec J Bs2 Acc MinBs}
      else Keepers in
        Keepers = for collect:C A in Acc do
                    if {Not {BranchIsSmaller J B A}} then {C A} end
                  end
        {MinimizeBranchSetRec J Bs2 B|Keepers MinBs}
      end
    else MinBs = Acc end
  end
  
  %  Utility procedures for generating lists of events of different types.
  %
  %    GetActions: get all ordinary action events (not finish actions)
  %    GetFinishes: get all finish events
  %
  proc {GetActions J Acts}
    Acts = {IntMap.allMatching J fun {$ I}
             D = {IntMap.get J I} in
             {Record.label D} == act andthen D.action \= finish
           end}
  end

  proc {GetFinishes J Fs}
    Fs = {IntMap.allMatching J fun {$ I}
             D = {IntMap.get J I} in
             {Record.label D} == act andthen D.action == finish
         end}
  end

  %  Check and correct any broken feasibility invariants introduced by
  %  the addition of a new action event AId.
  %
  %  We must perform the check not only for action AId itself, but also
  %  for any actions that do not preceed AId, as it may generate new histories
  %  for those actions which break their feasibility.
  %
  proc {FixFeasibility JIn AId JOut}
    As = {List.filter {GetActions JIn} fun {$ I} {Not {Preceeds JIn I AId}} end}
  in
    {FixActionFeasibility JIn As JOut}
  end

  %
  %  Fix feasibility invariants for each action event in the list Acts.
  %
  %  To do so, we find a minimal set of branches that are indistinguishable
  %  from that action's enablers.  Each such branch must enable a matching
  %  action event, which we insert if necessary.
  %
  proc {FixActionFeasibility JIn Acts JOut}
    case Acts of AId|As then
       A = {IntMap.get JIn AId}
       IBs = {IndistBranches JIn {Sitcalc.actor A.action} A.enablers}
       JOut2
      in
       JOut2 = {AddFeasibilityEvents JIn A IBs}
       % If the above call modifies the JE, then it will re-execute the
       % feasibility fixing routines and we don't need to continue the loop.
       if JOut2 == JIn then
         {FixActionFeasibility JIn As JOut}
       else
          JOut = JOut2
       end
    else
      JIn = JOut
    end
  end

  %
  %  Ensure that for each branch in IBs, there is an event corresponding
  %  to the action event A.
  %
  proc {AddFeasibilityEvents JIn Act IBs JOut}
    case IBs of B|Bs then EAct in
      %
      % Try to find an appropriate event already in the JE
      %
      EAct = {IntMap.nextMatching JIn 0 fun {$ I} 
                        Data = {IntMap.get JIn I} in
                        if {Record.label Data} == act then
                          Data.enablers == B andthen Data.action == Act.action
                        else false end 
                     end}
      %
      % If there isn't one, we must insert one
      %
      if EAct == nil then
        if {CannotInsertAfter JIn B} then
          fail
        else J2 in
          % We don't need to continue the loop, because this call will
          % re-invoke the feasibility fixing procedures.
          {InsertWithEnablers JIn B Act B J2 _}
          J2 = JOut
        end
      else
        {AddFeasibilityEvents JIn Act Bs JOut}
      end
    else JOut = JIn end
  end

  %
  %  Determine whether a new action can be inserted that is enabled by
  %  the events Ns.  This is false if there is a finish event following
  %  all events in the list - which indicates that all branches they are
  %  on are closed.
  %
  proc {CannotInsertAfter J Ns B}
    Fs = {GetFinishes J}
  in
    B = for return:R default:false F in Fs do Follows in
          Follows = for return:R default:true N in Ns do
                      if {Not {Preceeds J N F}} then {R false} end
                    end
          if Follows then {R true} end
        end
  end

  %
  %  Assert that the given action is in the execution at event N.
  %  This is analogous to {Insert} but instead of adding new actions,
  %  it verifies existing ones.
  %
  proc {Assert J Lf N S Preceeds Outcomes}
    Data = {IntMap.get J N}
    Outs
  in
    Data.action = S.action
    Data.enablers = {FindEnablingEvents J S.action Lf Preceeds}
    Outs = {Sitcalc.outcomes S}
    {List.length Outs} = {List.length Data.outcomes}
    for O1 in Outs O2 in Data.outcomes do
      OData = {IntMap.get J O2} in
      OData.out = O1.out
    end
    Outcomes = for collect:C I in Data.outcomes do
                 {C {BranchPush J I Lf}}
               end
  end

  %
  %  Insert special 'finish' action to close the leaf Lf
  %
  proc {Finish JIn Lf JOut}
    FEvent = act(action:finish enablers:Lf outcomes:nil)
  in
    JOut = {IntMap.append JIn FEvent}
  end

  %
  %  Determine the next-oldest action event in the execution that
  %  could extend the branch Ns. This will be nil if there is no such
  %  action, or an event identifier otherwise.
  %
  fun {NextEvent J Ns}
    I0 = if Ns == nil then ~1 else Ns.1 end in
    {IntMap.nextMatching J I0 fun {$ I} {Not {ConflictsB J I Ns}} end}
  end

  %
  %  Extract the observation data from last event in Ns into the record
  %  S.  The result is a record identical to S except that 'out' is
  %  the observations in the outcome event, and 'seqn' is the event
  %  number.
  %
  proc {Getout J Ns SIn SOut}
    Data = {IntMap.get J Ns.1}
  in
    SOut = {Record.adjoinList SIn [out#Data.out seqn#Ns.1]}
  end


  %  Lazily generate a list of all events E for which must preceed the
  %  given event.  There may be duplicate entries.
  %
  fun lazy {Preceeders J N}
    Data = {IntMap.get J N}
  in
    case Data of act(...) then {PreceedersRec J Data.enablers}
    else if Data.act == nil then nil
         else Data.act|{Preceeders J Data.act} end
    end
  end

  fun lazy {PreceedersRec J Ns}
    case Ns of N|NTail then
      N|{LazyAppend {Preceeders J N} {PreceedersRec J NTail}}
    else nil end
  end

  fun lazy {LazyAppend L1 L2}
    if L1 == nil then L2
    else L1.1|{LazyAppend L1.2 L2} end
  end


  %  Generate the preceeders of the given event that are observable
  %  by the given agent.
  %
  proc {PreceedersAgt J Agt E PAs}
    Ps = {Preceeders J E} in
    PAs = {List.filter Ps fun {$ I}
            Data = {IntMap.get J I} in
            case Data of act(...) then
              {Sitcalc.actor Data.action} == Agt
            else
              Data.out.Agt \= nil
            end
          end}
  end

  %  Determine whether event N1 must preceed event N2. We can shortcut
  %  some cases since we know that larger IDs cannot preceed smaller
  %  IDs.
  %
  proc {Preceeds J N1 N2 B}
    if N1 >= N2 then B = false
    else B = {List.member N1 {Preceeders J N2}} end
  end

  %  Determine whether events N1 and N2 are in conflict.
  %  This is true if a pair of preceeders are in direct conflict, that
  %  is, they are alternate outcomes of the same action.
  %
  proc {Conflicts J N1 N2 B}
    if N1 == N2 then B = false
    else
      B = for return:R default:false P1 in N1|{Preceeders J N1} do
            for P2 in N2|{Preceeders J N2} do
              if P1 \= P2 then D1 D2 in
                D1 = {IntMap.get J P1}
                D2 = {IntMap.get J P2}
                if {Record.label D1}==out andthen {Record.label D2}==out then
                  if D1.act == D2.act then {R true} end
                end
              end
            end
          end
    end
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


  %  Search for a common view of branches B1 and B2 from persective of Agt.
  %  We achieve this by selecting and performing enabled events with
  %  identical observations, until we are able to fully execute both
  %  branches.
  %
  proc {FindCommonView J Agt B1 B2 V}
    {FindCommonViewRec J Agt B1#J B2#J V}
  end

  proc {FindCommonViewRec J Agt B1#J1 B2#J2 V}
    %  Branches must be fully executed at the same time, so
    %  fail if one is empty and the other is not.
    if B1 == nil then
      if B2 \= nil then
        fail
      end
    elseif B2 == nil then
      fail
    else A1 O1 A2 O2 Obs1 Obs2 B1n B2n J1n J2n in
      %  Otherwise, we select an enabled event following each branch,
      %  and ensure matching observations.
      A1#O1 = {FindActiveEventAgt J1 Agt}
      A2#O2 = {FindActiveEventAgt J2 Agt}
      {ConflictsB J1 O1 B1 false}
      {ConflictsB J2 O2 B2 false}
      Obs1 = {IntMap.get J1 O1}.out.Agt
      Obs2  = {IntMap.get J2 O2}.out.Agt
      Obs1 = Obs2
      J1n = {PerformEvent {PerformEvent J1 A1} O1}
      J2n = {PerformEvent {PerformEvent J2 A2} O2}
      B1n = {List.subtract B1 O1}
      B2n = {List.subtract B2 O2}
      V = Obs1|{FindCommonViewRec J Agt B1n#J1n B2n#J2n}
    end
  end


  %  Find an Action#Outcome event pair that could be active from
  %  the perspective of Agt.
  %
  proc {FindActiveEventAgt J Agt A#O}
    Acts Outs in
    Acts = {IntMap.allMatching J fun {$ I}
             Data = {IntMap.get J I} in
             {Record.label Data} == act andthen
             {PreceedersAgt J Agt I} == nil
           end}
    {LP.member A Acts}
    Outs = {IntMap.get J A}.outcomes
    {LP.member O Outs}
    ({IntMap.get J O}.out.Agt \= nil)=true
  end

  %  Given a branch B, determine a minimal set of other branches Bs
  %  that would be indistinguishable from the perspective of agent Agt.
  %  For the moment, brute force is used to check for generation of
  %  identical histories.
  %
  proc {IndistBranches J Agt B Bs}
    AllBranches = {FindIndistBranches J Agt B} in
    Bs = {MinimizeBranchSet J AllBranches}
  end

  proc {FindIndistBranches J Agt B Bs}
    %  A branch indistinguishable from B must contain an event with
    %  a matching observation to each event from the input branch.
    %  We generate all such branches and test whether they can in fact
    %  generate an indistinguishable history.
    %  
    PossBs = {List.subtract {GeneratePossIndistBranches J Agt B} B} in
    Bs = for collect:C B2 in PossBs do
      if {BranchesAreIndist J Agt B B2} then
        {C B2}
      end
    end
  end 

  proc {GeneratePossIndistBranches J Agt B Bs}
    case B of N|Ns then
      Out1 = {IntMap.get J N}
      N2s = {IntMap.allMatching J fun {$ I}
              Out2 = {IntMap.get J I} in
              {Record.label Out2} == out andthen
              Out2.out.Agt == Out1.out.Agt
            end}
      in
      Bs = for collect:C B2 in {GeneratePossIndistBranches J Agt Ns} do
        for N2 in N2s do
            if {Not {ConflictsB J N2 B2}} then
              {C {BranchPush J N2 B2}}
            end
        end
      end
    else Bs = [nil] end
  end

  proc {BranchesAreIndist J Agt B1 B2 B}
    B = ({Search.base.one proc {$ V}
      {FindCommonView J Agt B1 B2 V}
    end} \= nil)
  end

  %  Roll the execution forward to directly after the performance
  %  of the given event.  If the event has preceeders, they will
  %  also be performed.
  %
  proc {PerformEvent JIn E JOut}
    P = {Preceeders JIn E}
  in
    case P of P1|_ then
      {PerformEvent {PerformEvent JIn P1} E JOut}
    else
      D = {IntMap.get JIn E} in
      case D of act(...) then
        J2 = {IntMap.drop JIn E} in
        JOut = {PerformEventOuts J2 D.outcomes}
      else
        J2 = {DropConflictingEvents JIn E} in
        JOut = {IntMap.forEach {IntMap.drop J2 E} proc {$ I V}
                 Data = {IntMap.get J2 I} in
                 if {Record.label Data} == act then
                   V = {Record.adjoinAt Data enablers
                           {List.subtract Data.enablers E}}
                 else V = Data end
               end}
      end
    end
  end

  %  Utility function to update the outcome events of a just-performed
  %  action event.
  %
  proc {PerformEventOuts JIn Outs JOut}
    case Outs of O|Os then
      Data = {IntMap.get JIn O}
      J2 = {IntMap.put JIn O {Record.adjoinAt Data act nil}} in
      {PerformEventOuts J2 Os JOut}
    else JOut = JIn end
  end

  %  Remove all event from the execuction that conflict with E.
  %
  fun {DropConflictingEvents JIn E}
    ToDrop = {IntMap.allMatching JIn fun {$ I}
                {Conflicts JIn I E}
             end}
  in
    {IntMap.dropAll JIn ToDrop}
  end


  %%%%%%%%%%%%%%
  %%
  %%  Everything following is code for outputing the graph,
  %%  not manipulating it.

  %
  %  Write a Graphviz dot-file representing the joint execution.
  %  File can be any object supporting the 'write' method.
  %
  %  We suppress outcome nodes that where they are the only outcome
  %  for that action.
  %
  proc {WriteDotFile J File}
    {File write(vs: "digraph G {\n")}
    {IntMap.forEach J
       proc {$ N Data}
          Data = {IntMap.get J N}
       in
         case Data of act(...) then
           {File write(vs: "n"#N#" [shape=ellipse,label=\""#{Value.toVirtualString Data.action ~1 ~1}#"\"];\n")}
           for E in Data.enablers do
             if {SuppressOutput J E} then
               {File write(vs: "n"#{IntMap.get J E}.act#" -> n"#N#";\n")}
             else 
               {File write(vs: "n"#E#" -> n"#N#";\n")}
             end
           end
           for O in Data.outcomes do
             if {Not {SuppressOutput J O}} then
               {File write(vs: "n"#N#" -> n"#O#";\n")}
             end
           end
         else
           if {Not {SuppressOutput J N}} then
             {File write(vs: "n"#N#" [shape=box,label=\""#{OutcomeLabel Data}#"\"];\n")}
           end
         end
       end
    } = _
    {File write(vs: "}\n")}
  end

  proc {SuppressOutput J O B}
    OData = {IntMap.get J O}
  in
    if {List.length {IntMap.get J OData.act}.outcomes} > 1 then
      B = false
    else B = true end
  end

  proc {OutcomeLabel OData Lbl}
    Lbls
  in
    Lbls = for collect:C Agt in {Record.arity OData.out} do
             if OData.out.Agt \= nil then
               {C Agt#": "#{Value.toVirtualString OData.out.Agt ~1 ~1}#"\\n"}
             end
           end
    Lbl = {List.toTuple '#' Lbls}
  end

end
