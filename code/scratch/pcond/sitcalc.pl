

%
%  simplify(+F1,-F2) - simpfily a fluent expression
%  
%  This predicate applies some basic simplification rules to a fluent
%  to eliminate redundancy and (hoepfully) speed up future reasoning.
%
simplify(P & Q,S) :-
    simplify(P,SP),
    simplify(Q,SQ),
    (
        SP=false, S=false
    ;
        SQ=false, S=false
    ;
        SP=true, S=SQ
    ;
        SQ=true, S=SP
    ;
        ground(SP), ground(SQ), SP=SQ, S=SP
    ;
        S= (SP & SQ)
    ), !.
simplify(P | Q,S) :-
    simplify(P,SP),
    simplify(Q,SQ),
    (
        SP=true, S=true
    ;
        SQ=true, S=true
    ;
        SP=false, S=SQ
    ;
        SQ=false, S=SP
    ;
        ground(SP), ground(SQ), SP=SQ, S=SP
    ;
        S= (SP | SQ)
    ), !.
simplify(-P,S) :-
    simplify(P,SP),
    (
        SP=false, S=true
    ;
        SP=true, S=false
    ;
        SP = -P2, S=P2
    ;
        S = -SP
    ), !.
simplify(all(X,P),S) :-
    simplify(P,SP),
    (
        SP=false, S=false
    ;
        SP=true, S=true
    ;
        S=all(X,SP)
    ), !.
simplify(exists(X,P),S) :-
    simplify(P,SP),
    (
        SP=false, S=false
    ;
        SP=true, S=true
    ;
        S=exists(X,SP)
    ), !.
simplify(P,P).


%
%  consequence(+F1,+F2) - Fluent F2 is a consequence of fluent F1
%
%  This predicate employs full first-order reasoning to determine whether
%  the fluent expression F1 logically entails the fluent expression F2.
%
consequence(P1,P2) :-
    % TODO: unique names axioms, etc
    Fml = ((true & -false & P1) -> P2),
    tautology(Fml).

%
%  joinlist(+Op,+In,-Out) - join items in a list using given operator
%
joinlist(_,[H],H).
joinlist(O,[H|T],J) :-
    T \= [],
    joinlist(O,T,TJ),
    J =.. [O,H,TJ].

%
%  eps_p(+F,+ADP,?Act,?Cond) - conditions for a fluent becoming true
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made true by the action Act.  If ADP is
%  not 'true', it specifies an action description predicate that must also
%  be satisfied.
%
eps_p(P,C,A,E) :-
    setof(Et,eps_p1(P,C,A,Et),Ets),
    joinlist((|),Ets,Etmp),
    simplify(Etmp,E).

%
%  eps_n(+F,+ADP,?Act,?Cond) - conditions for a fluent becoming false
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made false by the action Act.  If ADP is
%  not 'true', it specifies an action description predicate that must also
%  be satisfied.
%
eps_n(P,C,A,E) :-
    setof(Et,eps_n1(P,C,A,Et),Ets),
    joinlist((|),Ets,Etmp),
    simplify(Etmp,E).

%
%  eps_p1(+F,+ADP,?Act,?Cond) - individual conditions for truthifying a fluent
%
%  This preciate enumerates the different ways in which the fluent F can become
%  true, which are collected by eps_p/4.
%
eps_p1((P & Q),C,A,E) :-
    eps_p(P,C,A,EP),
    eps_p(Q,C,A,EQ),
    E = (EP & EQ).
eps_p1((P & Q),C,A,E) :-
    eps_p(P,C,A,EP),
    eps_n(Q,C,A,EQn),
    E = (EP & Q & -EQn).
eps_p1((P & Q),C,A,E) :-
    eps_n(P,C,A,EPn),
    eps_p(Q,C,A,EQ),
    E = (P & -EPn & EQ).
eps_p1((P & Q),C,A,E) :-
    eps_p(P,C,A,EP),
    \+ eps_n(Q,C,A,_),
    E = (EP & Q).
eps_p1((P & Q),C,A,E) :-
    eps_p(Q,C,A,EQ),
    \+ eps_n(P,C,A,_),
    E = (P & EQ).

eps_p1((P | _),C,A,E) :-
    eps_p(P,C,A,E).
eps_p1((_ | Q),C,A,E) :-
    eps_p(Q,C,A,E).

eps_p1(-P,C,A,E) :-
    eps_n(P,C,A,E).

eps_p1(all(X,P),C,A,E) :-
    subs(X,Y,P,Ps),
    eps_p(Ps,C,A,EP),
    eps_n(Ps,C,A,EPn),
    E = all(X,((P & -(EPn & X=Y)) | (EP & X=Y))).
eps_p1(all(X,P),C,A,E) :-
    subs(X,Y,P,Ps),
    eps_p(Ps,C,A,EP),
    \+ eps_n(Ps,C,A,_),
    E = all(X,(P | (EP & X=Y))).

eps_p1(exists(X,P),C,A,E) :-
    subs(X,Y,P,Ps),
    eps_p(Ps,C,A,EP),
    E = exists(X,EP & X=Y).

eps_p1(P,C,A,E) :-
    prim_fluent(P),
    prim_action(A),
    causes_true(P,A,Et),
    ( C=true ->
        E = Et
    ;
        adp_fluent(C,A,Ea),
        E = (Ea & Et)
    ).


%
%  eps_n1(+F,+ADP,?Act,?Cond) - individual conditions for falsifying a fluent
%
%  This preciate enumerates the different ways in which the fluent F can become
%  false, which are collected by eps_n/4.
%
eps_n1((P & _),C,A,E) :-
    eps_n(P,C,A,E).
eps_n1((_ & Q),C,A,E) :-
    eps_n(Q,C,A,E).

eps_n1((P | Q),C,A,E) :-
    eps_n(P,C,A,EP),
    eps_n(Q,C,A,EQ),
    E = (EP & EQ).
eps_n1((P | Q),C,A,E) :-
    eps_n(P,C,A,EP),
    eps_p(Q,C,A,EQp),
    E = (EP & -Q & -EQp).
eps_n1((P | Q),C,A,E) :-
    eps_p(P,C,A,EPp),
    eps_n(Q,C,A,EQ),
    E = (-P & -EPp & EQ).
eps_n1((P | Q),C,A,E) :-
    eps_n(P,C,A,EP),
    \+ eps_p(Q,C,A,_),
    E = (EP & -Q).
eps_n1((P | Q),C,A,E) :-
    eps_n(Q,C,A,EQ),
    \+ eps_p(P,C,A,_),
    E = (-P & EQ).

eps_n1(-P,C,A,E) :-
    eps_p(P,C,A,E).

eps_n1(all(X,P),C,A,E) :-
    subs(X,Y,P,Ps),
    eps_n(Ps,C,A,EP),
    E = exists(X,EP & X=Y).

eps_n1(exists(X,P),C,A,E) :-
    subs(X,Y,P,Ps),
    eps_n(Ps,C,A,EP),
    eps_p(Ps,C,A,EPp),
    E = all(X,((-P & -(EPp & X=Y)) | (EP & X=Y))).
eps_n1(exists(X,P),C,A,E) :-
    subs(X,Y,P,Ps),
    eps_n(Ps,C,A,EP),
    \+ eps_p(Ps,C,A,_),
    E = all(X,(-P | (EP & X=Y))).

eps_n1(P,C,A,E) :-
    prim_fluent(P),
    prim_action(A),
    causes_false(P,A,Et),
    ( C=true ->
        E = Et
    ;
        adp_fluent(C,A,Ea),
        E = (Ea & Et)
    ).


%
%  regression(+F,+A,-Fr) - Fr is the regression of F over action A
%
%  This predicate calculates the regression of a fluent F with respect to
%  an action A, yielding a new fluent Fr.  Currently, A must be ground.
%

regression(F,A,Fr) :-
    (eps_p(F,true,A,Ep) -> Ep=Ep ; Ep=false),
    (eps_n(F,true,A,En) -> En=En ; En=false),
    simplify(Ep | (F & -En),Fr).

%
%  holds(+F,+S) - fluent F holds in situation S
%
%  This predicate is true whenever the fluent F holds in situation S.
%
holds(true,_).
holds(F,do(A,S)) :-
    regression(F,A,Fr),
    holds(Fr,S).
holds(F1 & F2,s0) :-
    holds(F1,s0), holds(F2,s0).
holds(F1 | F2,s0) :-
    holds(F1,s0) ; holds(F2,s0).
holds(all(V,F),s0) :-
    holds(-exists(V,-F),s0).
holds(exists(V,F),s0) :-
    subs(V,_,F,F1), holds(F1,s0).
holds(-(F1 & F2),s0) :- 
    holds((-F1) | (-F2),s0).
holds(-(F1 | F2),s0) :-
    holds((-F1) & (-F2),s0).
holds(-all(V,F),s0) :-
    holds(exists(V,F),s0).
holds(-exists(V,F),s0) :-
    \+ holds(exists(V,F),s0).
holds(F,s0) :-
    prim_fluent(F), 
    initially(F).

%
%  subs(Name,Value,Old,New):  substitue values in a term
%
%  This predicate is true when New is equal to Old with all occurances
%  of Name replaced by Value - basically, a symbolic substitution
%  routine.  For example, it is usually used to produce a result such
%  as:
%
%      subs(now,S,fluent(now),fluent(S)).
%
subs(_,_,T,Tr) :-
    var(T), Tr = T.
subs(X,Y,T,Tr) :-
    \+ var(T), T = X, Tr = Y.
subs(X,Y,T,Tr) :-
    T \= X, T =.. [F|Ts], subs_list(X,Y,Ts,Trs), Tr =.. [F|Trs].

%
%  subs_list(Name,Value,Old,New):  value substitution in a list
%
%  This predicate operates as sub/4, but Old and New are lists of terms
%  instead of single terms.  Basically, it calls sub/4 recursively on
%  each element of the list.
%
subs_list(_,_,[],[]).
subs_list(X,Y,[T|Ts],[Tr|Trs]) :-
    subs(X,Y,T,Tr), subs_list(X,Y,Ts,Trs).


