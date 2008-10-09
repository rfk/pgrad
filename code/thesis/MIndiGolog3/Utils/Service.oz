%
%  Service.oz:  Simple port-based service implementation
%
%  This functor provides the ability to turn a function into a service -
%  that is, a thread running in the top-level space and responding to
%  queries on a port.  This allows the function to handle mutablestate
%  from within subordinated spaces.
%
%  The function to be serviceized must take a single argument.  This can,
%  of course, be a list of actual arguments.
%

functor

export

  New

define

  proc {New Func Serv}
    IStream
    IPort = {Port.new IStream}
  in
    thread
      for In#Out in IStream do
        Out = {Func In}
      end
    end
    proc {Serv In Out}
      Out = !!{Port.sendRecv IPort In}
    end
  end

end
