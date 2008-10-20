%
%  Control.oz:  procedures for controlling an individual team-member
%
%  Copyright 2008, Ryan Kelly
%
%  This file manages communication between individual instances of the
%  interpreter, representing different team members.  The top-level control
%  file should call {Control.init}, which will establish the necessary
%  inter-agent communication links.
%
%  Things are slightly complicated by the fact that communication cannot be
%  performed from within a subordinated computation space, meaning that it
%  cannot be performed from inside a Search object.  To get around this,
%  must use Mozart's Port objects to route communication out to a separate
%  thread running in the top-level computation space.
%

functor 

import

  LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
  Domain at '/storage/uni/pgrad/code/thesis/MIndiGolog1/Domain.ozf'

  System
  Connection
  Open
  Search

export

  TeamMember
  TeamLeader
  Agents
  Subordinates

  DoParallelSearch

  Init
  SendMessage
  WaitForMessage

  Log
  Execute

define

  %  We depend on the main script to bind these values to something
  %  useful, they are simply collected here for easy access.

  % Name of agent designated as team leader
  TeamLeader = _

  % Name of team member executing this program
  TeamMember = _

  % Whether or not to use the parallel search feature
  DoParallelSearch = _

  % Open-ended stream to which messages will be writen, and mutable
  % pointer to the (free) tail of the stream.
  Msgs = _
  MsgPntr = {Cell.new Msgs}

  % Port on which to perform initial team sync
  CommPort = 8013

  % List of all agents in the team, and all agents who are not the team
  % leader.  These will be bound when Init is called, by introsepcting the
  % definitions in Domain.oz
  Agents = _
  Subordinates = _

  %  Initialise the control structures.
  %  If the current agent is the team leader, it listens on the communication
  %  port waiting for the other team members to check in.  Other team members
  %  connect to the port and send their name, and the team leader replies
  %  with a ticket to the shared message stream.
  %
  %  Once all agents have checked in, the team leader sends a 'ready' message
  %  and everyone can start executing.
  %
  proc {Init}
    % Populate lists of agents and subordinates by intropsecting domain defns
    %
    Agents = {Search.base.all proc {$ Agt}
               {Domain.isAgent Agt}
             end}
    Subordinates = {Search.base.all proc {$ Agt}
                     {Domain.isAgent Agt}
                     (Agt == TeamLeader)=false
                   end}
    % Default to using parallel search if not already set otherwise
    %
    if {IsFree DoParallelSearch} then
      DoParallelSearch = true
    end
    %  Wait for all team members to check in
    %
    if TeamMember == TeamLeader then Tkt Skt Serve in
      % I am the team leader, create a ticket to the shared message
      % stream and serve it over TCP to all subordinate agents.
      Tkt = {Connection.offerUnlimited Msgs}
      Skt = {New Open.socket init}
      {Skt bind(takePort:CommPort)}
      {Skt listen}
      % Recursive loop, to serve the ticket to each subordinate agent
      proc {Serve Agents} CSkt AgtS Agt RemAgents in
        if Agents \= nil then
          {Log waiting_for(Agents)}
          % Accept an incoming request from a team member
          {Skt accept(accepted: CSkt acceptClass:Open.socket)}
          % Read the agent's name from the connection.  If it's not in
          % the list remaining to serve, we just ignore it.
          {CSkt read(list: AgtS)}
          Agt = {String.toAtom AgtS}
          if {List.member Agt Agents} then
            % Send the ticket to the agent
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
      % Serve the ticket to all subordinate agents, then close the connection
      % and send a 'ready' message.
      {Serve Subordinates}
      {Skt close}
      {SendMessage ready}
    else Tkt Skt in
      % I am a subordinate, check in with the leader by sending my name
      % and recieving a ticket to the shared message stream.
      Skt = {New Open.socket init}
      {Skt bind}
      {Skt connect(port:CommPort host:TeamLeader)}
      {Skt write(vs: TeamMember)}
      {Skt shutDown(how: [send])}
      {Skt read(list: Tkt)}
      {Skt close}
      {Connection.take Tkt Msgs}
      % Wait for the 'ready' message indicating that everyone has checked in
      ({WaitForMessage} == ready)=true
    end
  end

  %  {SendMessage} allows the team leader to send a messge to subordinates,
  %  by writing it to the shared message stream.  Since we need to be able
  %  to do this from within a computation space, we must serialize the msg
  %  and route the function call through a port to top-level thread.
  %
  local
    IPort IStream
  in
    IPort = {Port.new IStream}
    thread
      for Msg in IStream do NewPntr in
        %  Bind the tail of the message stream to append the new message,
        %  and atomically update the pointer to the stream tail.
        {Cell.exchange MsgPntr (Msg|NewPntr) NewPntr}
      end
    end
    proc {SendMessage Msg}
      {Port.send IPort {LP.serialize Msg}}
    end
  end 

  %  {WaitForMessage} lets subordinate agents wait for a message from leader.
  %  Like {SendMessage}, this needs to operate via a Port so it can be called
  %  in a computation space.  Since it is receiving data from the top-level
  %  space, it must use Port.sendRecv.
  %
  local
    IPort IStream
  in
    IPort = {Port.new IStream}
    thread
      for unit#Msg in IStream do NextMsg in
        % Wait for the current tail pointer to be bound to a value
        {Cell.access MsgPntr NextMsg}
        {Value.wait NextMsg}
        % Update the tail pointer to reference the new tail
        {Cell.exchange MsgPntr _ NextMsg.2}
        Msg = NextMsg.1
      end
    end
    proc {WaitForMessage Msg}
      Msg1 = !!{Port.sendRecv IPort unit}
    in
      % Wait for the variable to actually be bound in the top-level thread
      {Value.wait Msg1}
      Msg = {LP.unserialize Msg1}
    end
  end 

  %  Log a message - just shows it on stdout.
  %
  proc {Log Msg}
    {System.show Msg}
  end

  %  Execute an action.
  %  Since we're not actually connected to anything, just print it to screen.
  %  We want to print do(C T) but 'do' is an Oz keyword, so print it in parts.
  %
  proc {Execute C T}
    {System.print d}
    {System.show o(C T)}
  end
 

end

