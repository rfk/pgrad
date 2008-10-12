
  proc {Insert JIn Ns S MustPrec JOut Outcomes}
    PossEns = {FindEnablingEvents JIn S.action Ns MustPrec}
    Ens = {FilterEnablers JIn PossEns}
  in
    {InsertWithEnablers JIn Ns S Ens JOut Outcomes}
  end

  proc {InsertWithEnablers JIn Ns S Ens JOut Outcomes}
    Outs = {Sitcalc.outcomes S}
    AId|OIds = {IntMap.nextAvailLabels JIn S|Outs}
    J1 J2
  in
    J1 = {IntMap.append JIn act(action: S.action
                                enablers: Ens
                                outcomes: OIds)}
    J2 = {InsertOutcomes AId J1 Outs OIds}
    JOut = {FixActionInvariants J2 AId}
    Outcomes = for collect:C I in OIds do
                 {C {BranchPush JOut I Ns}}
               end
  end

