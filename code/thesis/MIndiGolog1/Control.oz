
functor 

import

  LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
  Domain at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Domain.ozf'


  System
  Connection
  Open
  Search

export

  Agents
  Init
  TeamLeader
  TeamMember
  SendMessage
  WaitForMessage

define

  % We depend on the main script to bind these values
  TeamLeader = _
  TeamMember = _

  % Stream to which messages will be written, and pointer to tail
  Msgs = _
  MsgPntr = {Cell.new Msgs}

  CommPort = 8017

  Agents = _
  Subordinates = _

  proc {Init}
    Agents = {Search.base.all proc {$ Agt}
               {Domain.isAgent Agt}
             end}
    Subordinates = {Search.base.all proc {$ Agt}
                     {Domain.isAgent Agt}
                     (Agt == TeamLeader)=false
                   end}
    if TeamMember == TeamLeader then Tkt Skt Serve in
      %  Open a socket on port CommPort.  Each incomming connection writes 
      %  its name to the socket, and we reply with the ticket.  Once all
      %  agents have checked in, we send a 'ready' message.
      %
      {Connection.offerUnlimited Msgs Tkt}
      Skt = {New Open.socket init}
      {Skt bind(takePort:CommPort)}
      {Skt listen}
      proc {Serve Agents} CSkt AgtS Agt RemAgents in
        {System.show waiting_for(Agents)}
        if Agents \= nil then
          {Skt accept(accepted: CSkt acceptClass:Open.socket)}
          {CSkt read(list: AgtS)}
          Agt = {String.toAtom AgtS}
          if {List.member Agt Agents} then
            RemAgents = {List.subtract Agents Agt}
            {CSkt write(vs: Tkt)}
          else
            RemAgents = Agents
          end
          {CSkt shutDown(how: [receive send])}
          {CSkt close}
          {Serve RemAgents}
        end
      end
      {Serve Subordinates}
      {Skt close}
      {SendMessage ready}
    else Tkt Skt Msg in
      Skt = {New Open.socket init}
      {Skt bind}
      {Skt connect(port:CommPort host:TeamLeader)}
      {Skt write(vs: TeamMember)}
      {Skt shutDown(how: [send])}
      {Skt read(list: Tkt)}
      {Skt close}
      {Connection.take Tkt Msgs}
      ({WaitForMessage} == ready)=true
    end
  end

  %  Sending messages needs to go out through top-level port
  %
  local
    SendPort SendStream
  in
    SendPort = {Port.new SendStream}
    thread
      for Msg in SendStream do NewPntr in
        {Cell.exchange MsgPntr (Msg|NewPntr) NewPntr}
      end
    end
    proc {SendMessage Msg}
      {Port.send SendPort {LP.serialize Msg}}
    end
  end 

  %  Receiving messages needs to come in through top-level port
  %
  local
    RecvPort RecvStream
  in
    RecvPort = {Port.new RecvStream}
    thread
      for unit#Msg in RecvStream do NewPntr Hd in
        {Cell.access MsgPntr Hd}
        {Value.wait Hd}
        {Cell.exchange MsgPntr _ Hd.2}
        Msg = Hd.1
      end
    end
    proc {WaitForMessage Msg}
      Msg1
    in
      Msg1 = !!{Port.sendRecv RecvPort unit}
      {Value.wait Msg1}
      Msg = {LP.unserialize Msg1}
    end
  end 

end

