
  proc {Insert JIn Ns S MustPrec JOut Outcomes}
    Ens = {FilterEnablers JIn {FindEnablingEvents JIn S.action Ns MustPrec}}
  in
    {InsertWithEnablers JIn Ns S Ens JOut Outcomes}
  end

  proc {InsertWithEnablers JIn Ns S Ens JOut Outcomes}
    Outs = {Sitcalc.outcomes S}
    AId|OIds = {IntMap.nextAvailLabels JIn S|Outs}
    J1 J2
  in
    J1 = {IntMap.append JIn act(action: S.action enablers: Ens outcomes: OIds)}
    J2 = {InsertOutcomes AId J1 Outs OIds}
    JOut = J2 %{FixActionInvariants J2 AId}
    Outcomes = for collect:C I in OIds do
                 {C {BranchPush JOut I Ns}}
               end
  end

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

