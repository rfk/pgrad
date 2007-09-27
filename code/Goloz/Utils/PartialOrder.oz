%
%  PartialOrder.oz
%
%  Implements a partial order.  Really?  Yes, really.
%  In particular, a partial order of events.  The order is built
%  up one event at a time.  Events inserted later cannot be ordered
%  before than those already in the order - they can only be after
%  or unordered.
%


functor

import

export

define

  %
  %  Initialize a new (empty) partial order structure
  %
  proc {Init P}
    P = po(count: 0
           events: nil
           after: nil)
  end

  %
  %  Insert a new event into the partial order.
  %  E is the event being inserted, and Order is a
  %  binary function that will be applied with E as
  %  first argument and another event from the order 
  %  as second argument.  It must return true when E
  %  is ordered after that event, false otherwise.
  %
  proc {Insert PIn E Order POut}
    PIn = POut
  end

end
