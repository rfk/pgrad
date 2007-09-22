%
%  PlanFront.oz:  Managing the front in a plan search
%
%  The search for a joint plan requires maintaining a "front" of in-progress
%  program executions and handling various queries regarding them.  This
%  functor provides a stateless data structure for doing so.
%
%  The PlanFront contains tuples E#D where E is an execution and D is
%  some additional (opaque) data about it.  Each entry in the front may
%  be either open (needs further execution) or closed (may terminate in
%  its current state).
% 

functor

import

  Execution

export

  Init
  Closed
  Select
  PopMatching
  Push

define

  %
  %  Initialize a PlanFront containing a single E#D entry
  %
  proc {Init E#D PF}
    PF = pf(
            open: [E#D]
            closed: nil
           )
  end

  %
  %  Checks whether a PlanFront is closed
  %
  proc {Closed PF B}
    B = (PF.open == nil)
  end

  %
  %  Select an open E#D entry.  Since all executions eventually need
  %  to be closed, we don't need to backtrack here - just return the
  %  first open execution.
  %
  proc {Select PF E#D}
    E#D = PF.open.1
  end

  %
  %  Get a list of all E#D entries that are indistinguishable from the
  %  given execution by at least one of the agents in Agts.  Removes
  %  the entries from the plan front - they will be expanded and pushed
  %  back into the front by the calling code.
  %
  proc {PopMatching PFIn Ex Agts Matches PFOut}
    MatchesO MatchesC LeftO LeftC
  in
    LeftO = {PopMatchingRec Ex Agts PFIn.open MatchesO}
    LeftC = {PopMatchingRec Ex Agts PFIn.closed MatchesC}
    Matches = {List.append MatchesO MatchesC}
    PFOut = {Record.adjoinList PFIn [open#LeftO closed#LeftC]}
  end 

  proc {PopMatchingRec Ex Agts Lst Matches Left}
    case Lst of E#D|Es then DoesMatch in
      DoesMatch = for return:R default:false Agt in Agts do O1 O2 in
                    O1 = {Execution.observations Ex Agt}
                    O2 = {Execution.observations Ex Agt}
                    if O1 == O2 then
                      {R true}
                    end
                  end
      if DoesMatch then Matches2 in
        Matches = E#D|Matches2
        {PopMatchingRec Ex Agts Es Matches2 Left}
      else Left2 in
        Left = E#D|Left2
        {PopMatchingRec Ex Agts Es Matches Left2}
      end
    else Left=nil Matches=nil end
  end


  %
  %  Push the given lists of entries onto the front.
  %
  proc {Push PFIn Open Closed PFOut}
    NewOpen NewClosed
  in
    NewOpen = {List.append PFIn.open Open}
    NewClosed = {List.append PFIn.closed Closed}
    PFOut = {Record.adjoinList PFIn [open#NewOpen closed#NewClosed]}
  end

end
