%
%  Agent.oz:  details of a specific agent
%
%  Each agent in the team has their identity described by a local
%  functor named "Agent".  This permits other functors to be shipped
%  to the agent and executed in its own context, rather than thinking
%  they're at the shipping agent.
%

functor

export

  Name

define

  Name = jim

end
