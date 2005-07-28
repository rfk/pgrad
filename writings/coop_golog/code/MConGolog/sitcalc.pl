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
%%    I am aware of an existing translation in Reiter's book "Knowledge
%%    in Action", but this was not refered to in producing this code.
%%
%%    The worlds modelled using this framework must conform to the
%%    following structural rules:
%%
%%       * All actions occur at a particular time, given as the
%%         last argument of the term.  Time is a real number.
%%
%%       * All actions are instantaneous.
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
%%       * specify the possibility axioms for both primitive and concurrent
%%         actions using poss/2.  It is the responsibility of the axiomatiser
%%         to take care of any interaction in the preconditions of possibly
%%         concurrent actions.
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
%%  actor(Act,Agt):  performin agent for Actions
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
    prim_action(A), functor(A,Func,Arity), arg(Arity,A,T).
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
coherent_time_check([],T).
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
    S = do(C,_), time(C,T).


%%
%%  precedes(S1,S2):  ordering over situations
%%
%%  This predicate is true when S2 is reachable from S1 by some finite
%%  sequence of actions.  Note that no situation precedes s0, by definition.
%%

precedes(_,s0) :- fail.
precedes(S1,do(C,S2)) :-
    poss(C,S2), precedes_eq(S1,S2), start(S2) =< time(C). 

%%
%%  precedes_eq(S1,S2):  precedes-or-equals
%%
%%  This predicate is to precedes/2 as <= is to < - it allows for the
%%  two arguments to be equal.
%%
precedes_eq(S1,S2) :-
    S1 = S2 ; precedes(S1,S2).


%%
%%  legal(S):   checks legality of a situation
%%
%%  A situation is considered legal if it properly precedes the situation
%%  before it, and any natural actions which could possibly have occured
%%  in the action bringing it about did in fact occur.
%%

legal(s0).
legal(do(C,S)) :-
    legal(S), poss(C,S), start(S) =< time(C),
    findall(A,legal_check_poss_nat(A,S),AllNA),
    legal_check_nat_occurs(AllNA,C,S).

%%
%%  legal_check_poss_nat(A,S):  find possible natural actions in S
%%
%%  This predicate checks that A is a natural action which is possible in
%%  situation S.  It can be used to enumerate all such possible actions.
%%
legal_check_poss_nat(A,S) :-
    natural(A), poss(A,S).

%%
%%  legal_check_nat_occurs(Acts,C,S):  check occurance of natural actions
%%
%%  This predicate checks the list Act of natural actions to ensure that
%%  each either occurs in the concurrent action C, or occurs at a later
%%  time than C.
%%
legal_check_nat_occurs([],_,_).
legal_check_nat_occurs([A|Acts],C,S) :-
    ( memberchk(A,C) ; time(C) < time(A) ),
    legal_check_nat_occurs(Acts,C,S).


%%
%%  poss(A,S):   possibility of executing an action
%%
%%  The predicate poss/2 must be true whenever it is possible to perform
%%  action A in situation S.  A may be either a primitve action or a list
%%  of concurrent actions.
%%
%%  The following example definition states that a concurrent action 
%%  consisting of a single primitive action is possible exactly when
%%  the primitive action is.
%%
poss([A],S) :-
    poss(A,S).

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

