%%
%%  sitcalc.pl:  Prolog Implementation of the Situation Calculus
%%
%%  Author:  Ryan Kelly (rfk)
%%
%%  Date Created:  12/03/07
%%
%%  To implement a domain axiomatisation using this framework, the following
%%  tasks must be completed:
%%
%%       * specify the primitive actions of the world using prim_action/1.
%%
%%       * specify the primitive fluents in the world using prim_fluent/1.
%%
%%       * specify the agents in the system using agent/1.
%%
%%       * specify the possibility axioms for primitive actions using poss/3.
%%
%%       * specify the successor state axioms in terms of predicates for
%%         each fluent.
%%
%%       * specify the initial conditions using fluent predicates with the
%%         situation term set to s0.
%%


%%
%%  prim_action(A):  define a primitive action
%%
%%  This predicate specifies the terms which represent primitive actions
%%  in the domain.  The following below are examples of both an agent-initiated
%%  and a natural "no-op" action.  As the action as no effect, successor
%%  state axioms are not necessary.
%%
prim_action(noop(A)) :-
    agent(A).
prim_action(noop).


%%
%%  actor(Actn,Agt):  performing agent for Actions
%%
%%  This predicate binds Agt to the agent performing primitive action Actn.
%%
actor(Actn,Agt) :-
    prim_action(Actn), arg(1,Actn,Agt).

%%
%%  precedes(S1,S2):  ordering over situations
%%
%%  This predicate is true when S2 is reachable from S1 by some finite
%%  sequence of actions.  Note that no situation precedes s0, by definition.
%%
precedes(_,s0) :- fail.
precedes(S1,do(A,S2)) :-
    poss(A,S2), precedes_eq(S1,S2).

%%
%%  precedes_eq(S1,S2):  precedes-or-equals
%%
%%  This predicate is to precedes/2 as <= is to <, it allows for the
%%  two arguments to be equal.
%%
precedes_eq(S1,S2) :-
    S1 = S2 ; precedes(S1,S2).

%%
%%  poss(A,S):   possibility of executing an action
%%
%%  The predicate poss/3 must be true whenever it is possible to perform
%%  action A in situation S.
%%
%%  The domain axiomatiser is required to provide implementations of
%%  poss/3 for all primitive actions.
%%


