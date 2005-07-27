
%%
%%  MConGolog:  ConGolog for multiple agents
%%
%%  This is a proof-of-concept implementation of a ConGolog semantics
%%  for multiple agents.  While traditional ConGolog provides the
%%  ability to execute several high-level programs concurrently via
%%  interleaving of their primitive actions, it does not provide for
%%  the concurrent execution of primitive actions.  This is required in
%%  order to take advantage of the parallelism offered by multi-agent
%%  systems.
%%


%%  Termination Rules

final(nil,_).

final(seq(D1,D2),S) :-
    final(D1,S), final(D2,S).

final(choice(D1,D2),S) :-
    final(D1,S)
    ;
    final(D2,S).

final(pi(V,D),S) :-
    sub(V,_,D,Dr), final(Dr,S).

final(star(_),_).

final(if(Cond,D1,D2),S) :-
    holds(Cond,S), final(D1,S)
    ;
    holds(neg(Cond),S), final(D2,S).

final(while(Cond,D),S) :-
    holds(neg(Cond),S)
    ;
    final(D,S).

final(conc(D1,D2),S) :-
    final(D1,S), final(D2,S).

final(pconc(D1,D2),S) :-
    final(D1,S), final(D2,S).

final(cstar(_),_).

%%  Transition Rules.

trans(C,S,nil,Sp) :-
    sub(now,S,C,CS), to_cact(CS,CA), poss(CA,S),Sp = do(CA,S).

trans(test(Cond),S,nil,S) :-
    holds(Cond,S).

trans(seq(D1,D2),S,Dp,Sp) :-
    Dp = seq(D1r,D2), trans(D1,S,D1r,Sp).
trans(seq(D1,D2),S,Dp,Sp) :-
    final(D1,S), trans(D2,S,Dp,Sp).

trans(choice(D1,D2),S,Dp,Sp) :-
    trans(D1,S,Dp,Sp) ; trans(D2,S,Dp,Sp).

trans(pi(V,D),S,Dp,Sp) :-
    sub(V,_,D,Dr), trans(Dr,S,Dp,Sp).

trans(star(D),S,Dp,Sp) :-
    Dp = seq(Dr,star(D)), trans(D,S,Dr,Sp).

trans(if(Cond,D1,D2),S,Dp,Sp) :-
    holds(Cond,S), trans(D1,S,Dp,Sp)
    ;
    holds(neg(Cond),S), trans(D2,S,Dp,Sp).

trans(while(Cond,D),S,Dp,Sp) :-
    Dp = seq(Dr,while(Cond,D)), holds(Cond,S), trans(D,S,Dr,Sp).

trans(conc(D1,D2),S,Dp,Sp) :-
    trans(D1,S,Ds1,do(C1,S)), trans(D2,S,Ds2,do(C2,S)),
    cact_union(C1,C2,CT), poss(CT,S),
    Dp = conc(Ds1,Ds2), Sp = do(CT,S)
    ;
    Dp = conc(Dr1,D2), trans(D1,S,Dr1,Sp)
    ;
    Dp = conc(D1,Dr2), trans(D2,S,Dr2,Sp).

trans(pconc(D1,D2),S,Dp,Sp) :-
    Dp = pconc(Dr1,D2), trans(D1,S,Dr1,Sp)
    ;
    Dp = pconc(D1,Dr2), trans(D2,S,Dr2,Sp), \+ trans(D1,S,_,_)
    ;
    D1 = seq(C1,Ds1), D2 = seq(C2,Ds2), Dp = pconc(Ds1,Ds2),
    cact_union(C1,C2,CT), poss(CT,S), Sp = do(CT,S).

trans(cstar(D),S,Dp,Sp) :-
    Dp = conc(Dr,cstar(D)), trans(D,S,Dr,Sp).


%%  Transitive Closure of Transition Rules

trans*(D,S,D,S).
trans*(D,S,Dp,Sp) :-
    trans(D,S,Dr,Sr), trans*(Dr,Sr,Dp,Sp).

%%  Definition of do()

do(D,S,Sp) :-
    trans*(D,S,Dp,Sp), final(Dp,Sp).

%%  Implementation of holds(Cond,Sit) predicate, with negation-as-failure

holds(and(C1,C2),S) :-
    holds(C1,S), holds(C2,S).
holds(or(C1,C2),S) :- 
    holds(C1,S)
    ;
    holds(C2,S).
holds(all(V,C),S) :-
    holds(neg(some(V,neg(C))),S).
holds(some(V,C),S) :-
    sub(V,_,C,Cr), holds(Cr,S).
holds(neg(neg(C)),S) :-
    holds(C,S).
holds(neg(and(C1,C2)),S) :-
    holds(or(neg(C1),neg(C2)),S).
holds(neg(or(C1,C2)),S) :-
    holds(and(neg(C1),neg(C2)),S).
holds(neg(all(V,C)),S) :-
    holds(some(V,neg(C)),S).
holds(neg(some(V,C)),S) :-
    \+ holds(some(V,C),S).
holds(P_Xs,S) :-
    P_Xs \= and(_,_),P_Xs \= or(_,_), P_Xs \= neg(_), P_Xs \= all(_,_),
    P_Xs \= some(_,_), sub(now,S,P_Xs,P_XsS), P_XsS.
holds(neg(P_Xs),S) :-
    P_Xs \= and(_,_),P_Xs \= or(_,_), P_Xs \= neg(_), P_Xs \= all(_,_),
    P_Xs \= some(_,_), sub(now,S,P_Xs,P_XsS), \+ P_XsS.

%%  Substitution of terms

sub(_,_,T,Tr) :-
    var(T), Tr = T.
sub(X,Y,T,Tr) :-
    \+ var(T), T = X, Tr = Y.
sub(X,Y,T,Tr) :-
    T \= X, T =.. [F|Ts], sub_list(X,Y,Ts,Trs), Tr =.. [F|Trs].

sub_list(_,_,[],[]).
sub_list(X,Y,[T|Ts],[Tr|Trs]) :-
    sub(X,Y,T,Tr), sub_list(X,Y,Ts,Trs).

%%  Implementation for Sets of Concurrent Actions (as lists)
%%  We assume there is no interaction between the possibility
%%  predicates, but that agents can only execute one action at a time.


is_cact([]).
is_cact([A|CT]) :-
    prim_action(A), is_cact(CT).

to_cact(C,C) :-
    is_cact(C).
to_cact(A,C) :-
    prim_action(A), C = [A].

cact_union(C1,C2,CT) :-
    to_cact(C1,C1A), to_cact(C2,C2A), cact_union_worker(C1A,C2A,CT).
cact_union_worker([],C2,C2).
cact_union_worker(C1,[],C1).
cact_union_worker(C1,[C2|C2t],CT) :-
    (member(C2,C1) ->
        cact_union_worker(C1,C2t,CT)
    ;
        cact_union_worker([C2|C1],C2t,CT)
    ).

poss([],_) :- fail.
poss([A|Ct],S) :-
    cact_poss([A|Ct],[],S).
cact_poss([],_,_).
cact_poss([A|Ct],Agents,S) :-
    poss(A,S), arg(1,A,Agent), \+ member(Agent,Agents),
    cact_poss(Ct,[Agent|Agents],S).
 

