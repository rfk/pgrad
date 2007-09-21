%
%  PlanFront.oz:  Managing the front in a plan search
%
%  The search for a joint plan requires maintaining a "front" of in-progress
%  program executions and handling various queries regarding them.  This
%  functor provides a stateless data structure for doing so.
%
%  The PlanFront contains tuples E#D#J where E is an execution, D is the
%  program remaining to be executed and J is a yet-to-be constructed joint
%  plan for the execution of D starting at E.  Each entry in the front
%  can be either open (needs further execution) or closed (may terminate
%  in its current state).
% 

functor

import

  LP at '../Utils/LP.ozf'
  Sitcalc at 'SitCalc.ozf'

export

  Init
  Closed
  Finish
  Select
  Matching
  Remove
  AddOpen
  AddClosed

define

  %
  %  Initialize a PlanFront containing a single E#D#J entry
  %
  proc {Init E#D#J PF}
    PF = pf(
            open: [E#D#J]
            closed: nil
           )
  end

  %
  %  Checks whether a PlanFront is closed
  %
  proc {Closed PF B}
    B = (PF.open == nil)
  end

  proc {Finish PF}
    for _#_#J in PF.closed do
      {Sitcalc.jplan.finish J}
    end
    skip
  end

  %
  %  Select an open E#D#J entry.  This procedure creates choicepoints
  %  for backtracking over the selection.
  %
  proc {Select PF E#D#J}
    {LP.member E#D#J PF.open}
  end

  %
  %  Get a list of all E#D#J entries that are indistinguishable from the
  %  given execution by at least one of the agents in Agts.
  %
  proc {Matching PF Ex Agts Matches}
    MatchesO MatchesC
  in
    MatchesO = for collect:C E#D#J in PF.open do
                 for break:B Agt in Agts do O1 O2 in
                   O1 = {Sitcalc.ex.observations Ex Agt}
                   O2 = {Sitcalc.ex.observations E Agt}
                   if O1 == O2 then
                     {C E#D#J} {B}
                   end
                 end
               end
    MatchesC = for collect:C E#D#J in PF.closed do
                 for break:B Agt in Agts do O1 O2 in
                   O1 = {Sitcalc.ex.observations Ex Agt}
                   O2 = {Sitcalc.ex.observations E Agt}
                   if O1 == O2 then
                     {C E#D#J} {B}
                   end
                 end
               end
    Matches = {List.append MatchesO MatchesC}
  end 


  %
  %  Remove the given E#D#J entries from the PlanFront
  %
  proc {Remove PF Pairs PFOut}
    case Pairs of H|Ps then O2 C2 PF2 in
      O2 = {List.subtract PF.open H}
      C2 = {List.subtract PF.closed H}
      PF2 = {Record.adjoinList PF [open#O2 closed#C2]}
      {Remove PF2 Ps PFOut}
    else PFOut = PF end
  end

  %
  %  Add the given E#D#J entries to the open list
  %
  proc {AddOpen PF Pairs PFOut}
    case Pairs of H|Ps then PF2 in
      PF2 = {Record.adjoinAt PF open H|PF.open}
      {AddOpen PF2 Ps PFOut}
    else PFOut = PF end
  end

  %
  %  Add the given E#D#J entries to the closed list
  %
  proc {AddClosed PF Pairs PFOut}
    case Pairs of H|Ps then PF2 in
      PF2 = {Record.adjoinAt PF closed H|PF.closed}
      {AddClosed PF2 Ps PFOut}
    else PFOut = PF end
  end

end

