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
%  A "branch of execution" is a partial run of execution that selects one
%  outcome for each action performed.  It is identified by a sorted list
%  of outcome event IDs, highest ID first.  A branch Ns must satisfy the
%  following constraint, ensuring it uniquely identifies a branch:
%
%    all N < Ns.1:  N in NS  xor
%                   (exists N' in Ns: Conflicts(N N') v Preceeds(N N'))
%
%  A special action labelled 'finish' is used to indicate that a branch
%  of execution has completed execution, and no more actions should be
%  added to it.
%
%


functor

import

  IntMap at '../Utils/IntMap.ozf'
  LP at '../Utils/LP.ozf'
  SitCalc
 
  System
  Open

export

  Init
  Insert
  Assert
  Finish
  NextEvent
  Getobs

  WriteDotFile
  WriteDotFileAgt
  Test

define

  %
  %  Initialize a new (empty) joint execution.
  %
  proc {Init J}
    J = {IntMap.init}
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
    AId|OIds = {IntMap.nextAvailLabels JIn S|Outs}
    J1 J2
  in
    J1 = {IntMap.append JIn act(action: S.action enablers: Ens outcomes: OIds)}
    J2 = {InsertOutcomes AId J1 Outs OIds}
    JOut = {FixActionInvariants J2 AId}
    Outcomes = for collect:C I in OIds do
                 {C {BranchPush JOut I Ns}}
               end
  end

  %
  %  Utility function to insert a list of outcome events into the joint exec.
  %
  proc {InsertOutcomes AId JIn Outs Ids JOut}
    case Outs of O|Os then J2 Is in
      Ids = _|Is
      J2 = {IntMap.append JIn out(obs: O.obs act: AId)}
      {InsertOutcomes AId J2 Os Is JOut}
    else JOut = JIn end
  end

  %
  %  Find the events that enable a new action event, by querying {MustPrec}.
  %  Ns is the branch after which the new event is being inserted, i.e.
  %  we assume that any events greater than Ns.1 conflict with the newly
  %  added event.
  %
  proc {FindEnablingEvents J Act Ns MustPrec Ens}
    case Ns of N|Nt then
      if {Orderable J N Act} then
        if {MustPrec N} then
          % Orderable, and must preceed, so it's an enabler.
          % We can ignore the enablers of Ns.1 in further queries.
          Ens = N|_
          {FindEnablingEvents J Act Nt MustPrec Ens.2}
        else
          % Orderable, but not required to preceed, so we get a choice point
          choice Ens = N|_
                 {FindEnablingEvents J Act Nt MustPrec Ens.2}
          []     {FindEnablingEvents J Act {BranchPop J Ns _} MustPrec Ens}
          end
        end
      else
        % Not orderable, so {MustPrec} must return false
        {MustPrec N} = false
        {FindEnablingEvents J Act {BranchPop J Ns _} MustPrec Ens}
      end
    else Ens = nil end
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
    elseif Data.obs.{SitCalc.actor Act} == nil then B = false
    else B = true end
  end

  %
  %  Convert a branch into the unique run of execution determined
  %  by order of insertion.  The run is generated lazily.
  %
  fun lazy {BranchToRun J Ns}
    if Ns == nil then
      now
    else H T in
      {BranchPop J Ns H T}
      ex({OutToStep J H} {BranchToRun J T})
    end
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
                if {Not {Preceeds J N2 N}} then
                  {C N2}
                end
              end
  in
    NsOut = {InsertInOrder N Keepers}
  end

  %
  %  Determine whether branch Ns1 is "smaller" than branch Ns2. 
  %  This means that everything in Ns1 is either also in Ns2,
  %  or preceeds something in Ns2.
  %
  proc {BranchIsSmaller J Ns1 Ns2 B}
    B = for return:R default:true N1 in Ns1 do Covered in
          Covered = for return:R2 default:false N2 in Ns2 do
                      if {Preceeds J N1 N2} then {R2 true} end
                      if N1 == N2 then {R2 true} end
                    end
          if {Not Covered} then {R false} end
        end
  end
  
  %
  %  Construct a step object representing the outcome event O.
  %  This will contain only the 'action' and 'obs' features, since that's
  %  all a joint execution knows about.  This is also the only information
  %  needed to reason about what holds after a run.
  %
  proc {OutToStep J O S}
    OData = {IntMap.get J O}
    AData = {IntMap.get J OData.act}
  in
    S = step(action:AData.action obs:OData.obs)
  end

  %
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

  %
  %  Check and correct any broken action invariants introduced by
  %  the addition of a new action event AId.
  %
  %  For now, this doesn't actually use the value of AId.  Figuring
  %  out how to use it to save time is an interesting topic for
  %  future research...
  %
  proc {FixActionInvariants JIn AId JOut}
    {FixInvariantActs JIn {GetActions JIn} JOut}
  end

  proc {WalkList L}
    case L of _|Ls then {WalkList Ls} else skip end
  end

  %
  %  Fix invariants for each action in the list Acts.
  %
  proc {FixInvariantActs JIn Acts JOut}
    {WalkList Acts}
    case Acts of A|As then
      D = {IntMap.get JIn A} Matches in
      Matches = {IndistinguishableSets JIn {SitCalc.actor D.action} D.enablers}
      {FixInvariantMatches JIn As D Matches JOut}
    else JIn = JOut end
  end

  %
  %  Ensure that for each entry in Matches, there is an event corresponding
  %  to the action event A.
  %
  proc {FixInvariantMatches JIn Acts Act Matches JOut}
    case Matches of M|Ms then MAct in
      MAct = {IntMap.nextMatching JIn 0 fun {$ I} 
                        Data = {IntMap.get JIn I} in
                        if {Record.label Data} == act then
                          Data.enablers == M andthen Data.action == Act.action
                        else false end 
                     end}
      if MAct == nil then
        if {CannotInsertAfter JIn M} then fail
        else J2 in
          {InsertWithEnablers JIn M Act M J2 _}
          % For the moment this is unnecessary, since {InsertWithEnablers}
          % will run {FixActionInvariants} all over again
          % {FixInvariantMatches J2 Acts Act Ms JOut}
          J2 = JOut
        end
      else
        {FixInvariantMatches JIn Acts Act Ms JOut}
      end
    else {FixInvariantActs JIn Acts JOut} end
  end

  %
  %  Given a set of outcome events Ns, determine all other sets of
  %  outcome events that would be indistinguishable from the perspective
  %  of agent Agt.  For the moment, brute force it used.
  %
  proc {IndistinguishableSets J Agt Ns Matches}
    AllBranches = {FindIndistinguishableBranches J Agt J#Ns [nil#J]} in
    Matches = {List.subtract {MinimizeBranchSet J AllBranches} Ns}
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
  %  This is an analogue to {Insert} but instead of adding new actions,
  %  it verifies existing ones.
  %
  proc {Assert J Ns N S Preceeds Outcomes}
    Data = {IntMap.get J N}
    Outs
  in
    Data.action = S.action
    Data.enablers = {FindEnablingEvents J S.action Ns Preceeds}
    Outs = {SitCalc.outcomes {BranchToRun J Ns} S}
    {List.length Outs} = {List.length Data.outcomes}
    for O1 in Outs O2 in Data.outcomes do
      OData = {IntMap.get J O2} in
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
    FEvent = act(action:finish enablers:Ns outcomes:nil)
  in
    JOut = {IntMap.append JIn FEvent}
  end

  %
  %  Determine the next-oldest action event in the execution that
  %  could extend the run Ns. This will be nil if there is no such
  %  action, or an event identifier otherwise.
  %
  fun {NextEvent J Ns}
    I0 = if Ns == nil then ~1 else Ns.1 end in
    {IntMap.nextMatching J I0 fun {$ I} {Not {ConflictsB J I Ns}} end}
  end

  %
  %  Extract the observation data from last event in Ns into the record
  %  S.  The result is a record identical to S except that 'obs' is
  %  the observations in the outcome event, and 'seqn' is the event
  %  number.
  %
  proc {Getobs J Ns SIn SOut}
    Data = {IntMap.get J Ns.1}
  in
    SOut = {Record.adjoinList SIn [obs#Data.obs seqn#Ns.1]}
  end


  %
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


  %
  %  Generate the preceeders of the given event that are observable
  %  by the given agent.
  %
  proc {PreceedersAgt J Agt E PAs}
    Ps = {Preceeders J E} in
    PAs = {List.filter Ps fun {$ I}
            Data = {IntMap.get J I} in
            case Data of act(...) then
              {SitCalc.actor Data.action} == Agt
            else
              Data.obs.Agt \= nil
            end
          end}
  end

  %
  %  Determine whether event N1 must preceed event N2. We can shortcut
  %  some cases since we know that larger IDs cannot preceed smaller
  %  IDs.
  %
  proc {Preceeds J N1 N2 B}
    if N1 >= N2 then B = false
    else B = {List.member N1 {Preceeders J N2}} end
  end

  %
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

  %
  %  List all the events which are currently active - that is, they
  %  have no preceeders left to fire.
  %
  proc {ActiveEvents J Evts}
    Evts = {IntMap.allMatching J fun {$ I} {Preceeders J I} == nil end}
  end

  %
  %  List all events that could be active from the perspective of the
  %  given agent.  
  % 
  proc {ActiveEventsAgt J Agt Evts}
    Evts = {IntMap.allMatching J fun {$ I}
      Data = {IntMap.get J I} in 
      {PreceedersAgt J Agt I} == nil andthen
      if {Record.label Data} == out then
        Data.obs.Agt \= nil
      else
        Data.action == finish orelse {SitCalc.actor Data.action} == Agt
      end
    end}
  end

  %
  %  Recursively generates the histories of observation produced by events
  %  in Ns, for agent Agt.  Hs is a list of tuples O#J2#Ns2 where O is the
  %  next act or obs made by the agent, J2 is the remaining execution, and
  %  Ns2 is the input events that have not yet been determined.
  %  Ns must contain only outcome events.
  %
  proc {GenerateHistories J Agt Ns Hs}
    if Ns == nil then Hs = nil
    else
      Active = {ActiveEventsAgt J Agt} in
      {WalkList Active}
      Hs = for collect:C E in Active do
             Data = {IntMap.get J E} in
             case Data of act(...) then
               J2 = {PerformEvent J E} in
               {C act(Data.action)#J2#Ns}
             else
               J2 = {PerformEvent J E}
               Ns2 = {List.subtract Ns E} in
               if {IntMap.hasLabels J2 Ns2} then
                 {C obs(Data.obs.Agt)#J2#Ns2}
               end
             end
           end
    end
  end

  proc {GetAllHistories J Agt Ns Hs}
    Hs = for collect:C (H#J2#Ns2) in {GenerateHistories J Agt Ns} do Hs2 in
      if Ns2 == nil then {C [H]}
      else
        Hs2 = {GetAllHistories J2 Agt Ns2}
        for H2 in Hs2 do
          {C H|H2}
        end
      end
    end
  end


  proc {FindIndistinguishableBranches JOrig Agt J#Ns SoFar IBs}
    if Ns == nil then 
      IBs = for collect:C B#_ in SoFar do {C B} end
    else Hs in
      Hs = {GenerateHistories J Agt Ns}
      IBs = for append:Acc (O#J2#Ns2) in Hs do NewSoFar Res in
        case O of act(Act) then 
             NewSoFar = for collect:C (Bsf#Jsf) in SoFar do
                        for E2#J2 in {PerformAct Jsf Act} do
                          {C {BranchPush JOrig E2 Bsf}#J2}
                        end
                      end
        []  obs(Obs) then
             NewSoFar = for collect:C (Bsf#Jsf) in SoFar do
                        for E2#J2 in {PerformObs Jsf Agt Obs} do
                          {C {BranchPush JOrig E2 Bsf}#J2}
                        end
                      end
        end
        Res = {FindIndistinguishableBranches JOrig Agt J2#Ns2 NewSoFar}
        {Acc Res}
      end
    end
  end

  proc {MinimizeBranchSet J Branches MinBs}
    {MinimizeBranchSetRec J Branches nil MinBs}
  end

  proc {MinimizeBranchSetRec J Branches Acc MinBs}
    case Branches of B|Bs then Covered in
      Covered = for return:R default:false A in Acc do
                  if {BranchIsSmaller J A B} then {R true} end
                end
      if Covered then {MinimizeBranchSetRec J Bs Acc MinBs}
      else Keepers in
        Keepers = for collect:C A in Acc do
                    if {Not {BranchIsSmaller J B A}} then {C A} end
                  end
        {MinimizeBranchSetRec J Bs B|Keepers MinBs}
      end
    else MinBs = Acc end
  end


  %
  %  Roll the execution forward by the given action label.  This
  %  generates a list of E#J pairs, where E is the event that was
  %  performed and J is the resulting execution.
  %
  proc {PerformAct JIn Act Outs}
    Es = {IntMap.allMatching JIn fun {$ I}
             D = {IntMap.get JIn I} in
             {Record.label D} == act andthen
             {Preceeders JIn I} == nil andthen
             D.action == Act
         end}
  in
    Outs = for collect:C E in Es do
              {C E#{PerformEvent JIn E}}
            end
  end

  %
  %  Roll the execution forward by the given observation label,
  %  from the perspective of the given agent.  The label can match
  %  any event with that label where all its {Preceeders} would be
  %  unobservable to Agt.
  %
  proc {PerformObs JIn Agt Obs Outs}
    Es = {IntMap.allMatching JIn fun {$ I}
           D = {IntMap.get JIn I} in
           {Record.label D} == out andthen
           D.obs.Agt == Obs andthen
           {PreceedersAgt JIn Agt I} == nil
         end}
  in
    Outs = for collect:C E in Es do
              {C E#{PerformEvent JIn E}}
            end
  end

  %
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

  proc {PerformEventOuts JIn Outs JOut}
    case Outs of O|Os then
      Data = {IntMap.get JIn O}
      J2 = {IntMap.put JIn O {Record.adjoinAt Data act nil}} in
      {PerformEventOuts J2 Os JOut}
    else JOut = JIn end
  end

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
  proc {WriteDotFile J File}
    {File write(vs: "digraph G {\n")}
    {IntMap.forEach J
       proc {$ N Data}
          Data = {IntMap.get J N}
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
    } = _
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

  proc {WriteDotFileAgt J Agt File}
    % TODO: JointExec.writeDotFileAgt
    skip
  end

  %%%%%%%%%%
  %%
  %%  test procedure
  %%

  proc {Test}
    J1 J2 J3 J4 J5 J6 J7 J8
    E1 E2 E3 E4 E5
  in
    {InsertWithEnablers {Init} nil s(action: acquire(thomas lettuce(1))) nil J1 _}
    {InsertWithEnablers J1 nil s(action: check_for(richard tomato)) nil J2 _}
    {Preceeders J2 0} = nil
    {Preceeders J2 1} = [0]
    {Preceeders J2 4} = [2]
    {Preceeds J2 2 4} = true
    {Preceeds J2 2 3} = true
    {Preceeds J2 1 3} = false
    {InsertWithEnablers J2 nil s(action: acquire(richard egg(1))) [4] J3 _}
    E1 = {LP.unDup {Preceeders J3 6}}
    E1 = [2 4 5]
    E2 = {LP.unDup {PreceedersAgt J3 thomas 6}}
    E2 = nil
    E3 = {LP.unDup {PreceedersAgt J3 richard 6}}
    E3 = E1
    {InsertWithEnablers J3 nil s(action: acquire(richard egg(1))) [3] J4 _}
    {InsertWithEnablers J4 nil s(action: acquire(thomas carrot(1))) [8] J5 _}
    {IntMap.get J5 11}.action = acquire(thomas carrot(1))
    {InsertWithEnablers J5 nil s(action: acquire(richard carrot(2))) [1 10] J6 _}
    {IntMap.get J6 15}.action = acquire(richard carrot(2))
    {WriteDotFile J6 {New Open.file init(name: 'test.dot' flags:[write create truncate])}}    
  end

end
