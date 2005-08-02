%%
%%  sitcalc.pl:  Prolog Implementation of the Concurrent, Temporal
%%               Situation Calculus with Natural Actions.
%%
%%  Author:  Ryan Kelly (rfk)
%%
%%  Date Created:  28/07/05
%%
%%    This implementation is a straight-forward translation of the
%%    work of Reiter ("Natural Actions, Concurrency and Continuous
%%    Time in the Situation Calculus") into prolog.  I can take no
%%    credit for the development of the Situation Calculus axioms,
%%    only for translating them into this code.
%%    I am aware of an existing implementation in Reiter's book "Knowledge
%%    in Action", but this was not refered to in producing this code.
%%
%%    The worlds modelled using this framework must conform to the
%%    following structural rules:
%%
%%       * All actions are instantaneous.
%%
%%       * All actions occur at a particular time, given as the
%%         last argument of the term.  Time is a real number.
%%
%%       * All actions are either "natural actions" or performed
%%         by an agent.  Natural actions are those for which the
%%         predicate natural(A) is true.
%%
%%       * For actions which are not natural, the first argument of
%%         the term must indicate the agent which performs that action.
%%
%%       * There is a unique initial situation denoted by the term s0.
%%
%%       * Concurrently occuring actions are represented as lists of
%%         primitive action terms.
%%
%%
%%  To implement a domain axiomatisation using this framework, the following
%%  tasks must be completed:
%%
%%       * specify the primitive actions of the world using prim_action/1.
%%
%%       * specify which actions are natural using natural/1.
%%
%%       * specify the primitive fluents in the world using prim_fluent/1.
%%
%%       * specify the agents in the system using agent/1.
%%
%%       * specify the possibility axioms for primitive actions using poss/2.
%%
%%       * specify conflicting sets of concurrent actions using conflicts/1.
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
prim_action(noop(A,_)) :-
    agent(A).
prim_action(noop(_)).

%%
%%  natural(A):  specify natural actions
%%
%%  For each natural action, this predicate must be defined to represent
%%  that fact.  Actions marked as natural must occur if it is possible for
%%  them to occur.
%%
natural(noop(_)).


%%
%%  actor(Act,Agt):  performing agent for Actions
%%
%%  This predicate binds Agt to the agent performing primitive action Act.
%%  It requires that the action not be natural, and that the agent be the
%%  first argument to the action term.
%%
actor(Act,Agt) :-
    prim_action(Act), \+ natural(Act), arg(1,Act,Agt).


%%
%%  time(A,T):  occurance time for actions
%%
%%  This predicate binds T to the occurance time of action A.  In the
%%  foundational axioms of the situation calculus, it is assumed that
%%  there is one such predicate defined for each primitive action in
%%  order to extract the time appropriately.  Here, the restriction that
%%  the time is given by the final argument and the term-introspection
%%  facilities of prolog are used to determine it without writing these
%%  predicates.
%%
%%  If A is bound to a coherent list of concurrent actions, the time is
%%  the occurance time of the first action in the list.
%%
%%  TODO: for efficiency, one could skip checking for coherency and
%%        instead assume it is enforced at a higher level
%%
time(A,T) :-
    prim_action(A), functor(A,_,Arity), arg(Arity,A,T).
time([A|C],T) :-
    coherent([A|C]), time(A,T).

%%
%%  coherent(C):  concurrent action C is coherent
%%
%%  For actions to be performed concurrently, they must all occur
%%  at the same time.  In addition, a concurrent action cannot be
%%  the empty set as this corresponds to doing nothing.  This
%%  predicate checks these conditions on lists of primitve actions.
%%
coherent([]) :- fail.
coherent([Head|Tail]) :-
    time(Head,T), coherent_time_check(Tail,T).

%%
%%  coherent_time_check(C,T):  check occurance times of concurrent actions
%%
%%  This predicte is true only if the occurance time of all actions in
%%  the list C is equal to the time T.
%%
coherent_time_check([],_).
coherent_time_check([Head|Tail],T) :-
    time(Head,T), coherent_time_check(Tail,T).

%%
%%  start(S,T):  start time of situation S
%%
%%  This predicate binds T to the start time of situation S.  This is
%%  defined as the occurance time of the last action performed in the
%%  situation.
%%
%%  The start time of s0 is not defined here, but could be defined by
%%  adding an additional clause for start/2.
%%
start(S,T) :-
    do(C,_) = S, time(C,T).


%%
%%  precedes(S1,S2):  ordering over situations
%%
%%  This predicate is true when S2 is reachable from S1 by some finite
%%  sequence of actions.  Note that no situation precedes s0, by definition.
%%

precedes(_,s0) :- fail.
precedes(S1,do(C,S2)) :-
    poss(C,S2), precedes_eq(S1,S2),
    start(S2,S2start), time(C,Ctime), S2start $=< Ctime.

%%
%%  precedes_eq(S1,S2):  precedes-or-equals
%%
%%  This predicate is to precedes/2 as <= is to < - it allows for the
%%  two arguments to be equal.
%%
precedes_eq(S1,S2) :-
    S1 = S2 ; precedes(S1,S2).


%%
%%  legal(S1,S2):  checks legality of situation progression
%%
%%  This predicate is true if the situation S2 can legally be reached
%%  from situation S1.  This means that for each transition from S1
%%  to S2, the performed actions were possible and there are no natural
%%  actions that could have occured but didnt.
%%
legal(S,S).
legal(S1,do(C,S2)) :-
    legal(S1,S2),
    poss(C,S2), start(S2,S2start), time(C,Ctime), S2start $=< Ctime,
    \+ ( natural(NA), poss(NA,S2), time(NA,NAtime),
         \+ memberchk(NA,C), NAtime $=< Ctime
       )
    .

%%
%%  legal(S):   checks legality of a situation
%%
%%  A situation is considered legal if it is legally reachable from the
%%  initial situation.  The initial situation itself is always legal.
%%
legal(s0) :- !.
legal(S) :-
    legal(s0,S).


%%
%%  poss(A,S):   possibility of executing an action
%%
%%  The predicate poss/2 must be true whenever it is possible to perform
%%  action A in situation S.  A may be either a primitve action or a list
%%  of concurrent actions.
%%
%%   The domain axiomatiser is required to provide implementations of
%%   poss/2 for all primitive actions.  Concurrent actions are considered
%%   possible if each constituent action is possible, and conflicts/2
%%   does not hold.
%%
poss([A],S) :-
    poss(A,S).
poss([A|C],S) :-
    poss_all([A|C],S), \+ conflicts([A|C],S).

%%
%%  poss_all(C,S):  all given actions are possible
%%
%%  This predicate checks that all primitive actions in concurrent action
%%  C are possible in situation S.  It is the basic possibility check
%%  for concurrent actions.
%%
poss_all([],_).
poss_all([A|C],S) :-
    poss(A,S), poss_all(C,S).


%%
%%  conflicts(C,S):  test for conflicting actions
%%
%%  This predicate is true if some of the primitive actions in concurrent
%%  action C cannot be executed together is situation S.  The clause
%%  below provides that an empty action never conflicts, other clasues
%%  must be supplied as appropriate.
%%
conflicts([],_) :- fail.

%%
%%  to_cact(A,C):   convert a primitive to a concurrent action
%%
%%  This predicate can be used as a "caste" operator to turn a primitve
%%  action A into concurrent action C by wrapping it in a list.  If A
%%  is already a concurrent action, it is simply unified with C.
%%
to_cact([],[]).
to_cact([H|T],[H|T]).
to_cact(A,C) :-
    prim_action(A), C = [A].


%%
%%  to_pact(Ain,Aout):  convert to a primitive action
%%
%%  This predicate allows the term Ain to be converted to a proper
%%  primitive action Aout.  It provides a syntactic shortcut for the
%%  specification of primitive actions:
%%
%%    * if Ain is already a valid primitive action, it is returned unchanged
%%    * if adding an additional argument to the end of Ain would make
%%      it a valid action, this is done and returned
%%    * if adding an additional argument to both the front and end of Ain
%%      would make it a valid action, this is done and returned.
%%
%%  Basically, this allows the time and agent arguments to be supressed in
%%  the representation of actions, when they are not of interest.
%%

to_pact(Ain,Ain) :-
    prim_action(Ain).
to_pact(Ain,Aout) :-
    Ain =.. [Func|Args],
    append(Args,[_],ArgsOutTest),
    AoutTest =.. [Func|ArgsOutTest],
    (prim_action(AoutTest) ->
        append(Args,[_],ArgsOut),
        Aout =.. [Func|ArgsOut]
    ).
to_pact(Ain,Aout) :-
    Ain =.. [Func|Args],
    append([_|Args],[_],ArgsOutTest),
    AoutTest =.. [Func|ArgsOutTest],
    (prim_action(AoutTest) ->
        append([_|Args],[_],ArgsOut),
        Aout =.. [Func|ArgsOut]
    ).

%%
%%  cact_union(C1,C2,CT):   create union of concurrent action sets
%%
%%  This predicate binds CT to the union of the action lists C1 and C2,
%%  removing any duplicate entries.  Both C1 and C2 may be primitive
%%  actions.
%%
cact_union(C1,C2,CT) :-
    to_cact(C1,C1A), to_cact(C2,C2A), cact_union_worker(C1A,C2A,CT).

%%  cact_union_worker(C1,C2,CT):   worker for cact_union/3
%%
%%  This predicate behaves as cact_union/3, but assumes that C1 and C2
%%  are proper lists of concurrent actions.
cact_union_worker([],C2,C2).
cact_union_worker(C1,[],C1).
cact_union_worker(C1,[C2|C2t],CT) :-
    (memberchk(C2,C1) ->
        cact_union_worker(C1,C2t,CT)
    ;
        cact_union_worker([C2|C1],C2t,CT)
    ).

