%
%  Agent.oz:  details of a specific agent
%
%  Each agent in the team has their identity described by a local
%  functor named "Agent".  This permits other functors to be shipped
%  to the agent and executed in its own context, rather than thinking
%  they're at the shipping agent.
%
%  TODO: better explanation of why this is important
%

functor

export

  name: Name

define

  Name = thomas

end