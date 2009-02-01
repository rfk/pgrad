
proc {FindEnablingEvents J Act Ns MustPrec Ens}
  case Ns of N|Nt then
    RemNs = {BranchPop J Ns _} in
    if {Orderable J N Act} then
      if {MustPrec N} then
        % Orderable, and must preceed, so it's an enabler.
        Ens = N|_
        {FindEnablingEvents J Act Nt MustPrec Ens.2}
      else
        % Orderable +  not must prec == choicepoint
        choice {FindEnablingEvents J Act RemNs MustPrec Ens}
        []     Ens = N|_
               {FindEnablingEvents J Act Nt MustPrec Ens.2}
        end
      end
    else
      % Not orderable, so {MustPrec} must return false
      {MustPrec N} = false
      {FindEnablingEvents J Act RemNs MustPrec Ens}
    end
  else Ens = nil end
end

