%
%  Execution.oz
%
%  Implements an execution, a partial order of events.
%


functor

import

export

  Init
  Insert
  Outcomes
  Holds

define

  %
  %  Initialize a new (empty) execution.
  %  Its history contains the single term 'now'.  Its future
  %  is initially empty.
  %
  proc {Init Ex}
    Ex = po(count: 0
           past: now
           future: nil
           after: nil)
  end

  %
  %  Insert a new event into the execution.
  %  E is the event being inserted, and Order is a
  %  binary function that will be applied with E as
  %  first argument and another event from the order 
  %  as second argument.  It must return true when E
  %  is ordered after that event, false otherwise.
  %
  proc {Insert ExIn E Order ExOut}
    ExIn = ExOut
  end

  %
  %  Step the execution forward one event.  This generates
  %  a list of executions, each of which are one possible
  %  evolution of the input execution.
  %
  proc {Step ExIn ExOuts}
    ExOuts = [ExIn]
  end

  %
  %  Access the last event to take place in the given execution.
  %
  proc {Last ExIn E}
    case Ex.past of H|T then  E = Ex.past.1
    else E = now end
  end

end
