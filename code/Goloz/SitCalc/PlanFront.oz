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
  Expand

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
  %  Expand the plan front by processing each entry.
  %  Then expansion function F is applied to each entry in the front.
  %  It returns a list of (Entry#Type) pairs where Type is either
  %  'open' or 'closed'.  The new front is then the concatentation of
  %  all these expansions.
  %
  proc {Expand PFIn F PFOut}
    NewOpen NewClosed NOTail1 NOTail2 NCTail1 NCTail2
  in
    {Expand_rec PFIn.open F NewOpen NewClosed NOTail1 NCTail1}
    {Expand_rec PFIn.closed F NOTail1 NCTail1 NOTail2 NCTail2}
    NOTail2 = nil NCTail2 = nil
    PFOut = pf(open: NewOpen closed: NewClosed)
  end

  proc {Expand_rec Exs F Open Closed OTail CTail}
    case Exs of E|Es then
      {Expand_collect {F E} Open Closed OTail CTail}
    else OTail=Open CTail=Closed end
  end

  proc {Expand_collect Exs Open Closed OTail CTail}
    case Exs of E#T|Es then
      if T == open then O2 in
        Open = E|O2
        {Expand_collect Es O2 Closed OTail CTail}
      else C2 in
        Closed = E|C2
        {Expand_collect Es Open C2 OTail CTail}
      end
    else OTail=Open CTail=Closed end
  end

end
