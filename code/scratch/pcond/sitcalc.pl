

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
consequence(F1,F2) :-
    copy_term(F1,F1p),
    copy_term(F2,F2p),
    fluent2term(F1p,0,N),
    fluent2term(F2p,N,_),
    % TODO: unique names axioms, etc
    Fml = ((true & -false & F1p) -> F2p),
    tautology(Fml).


fluent2term(F,N,N2) :-
    var(F),
    concat_atom([x,N],F),
    N2 is N + 1.
fluent2term(F,N,N) :-
    ground(F).
fluent2term(F,N,N2) :-
    nonvar(F), \+ ground(F),
    F =.. [_|Args],
    fluent2term_list(Args,N,N2).

fluent2term_list([],N,N).
fluent2term_list([H|T],N,N2) :-
    fluent2term(H,N,N3),
    fluent2term_list(T,N3,N2).
    

%
%  joinlist(+Op,+In,-Out) - join items in a list using given operator
%
joinlist(_,[H],H).
joinlist(O,[H|T],J) :-
    T \= [],
    joinlist(O,T,TJ),
    J =.. [O,H,TJ].

%
%  eps_p(+F,?Act,?Cond) - conditions for a fluent becoming true
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made true by the action Act.
%
eps_p(P,A,E) :-
    setof(Et,eps_p1(P,A,Et),Ets),
    joinlist((|),Ets,Etmp),
    simplify(Etmp,E).

%
%  eps_n(+F,?Act,?Cond) - conditions for a fluent becoming false
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made false by the action Act.
%
eps_n(P,A,E) :-
    setof(Et,eps_n1(P,A,Et),Ets),
    joinlist((|),Ets,Etmp),
    simplify(Etmp,E).

%
%  eps_p1(+F,?Act,?Cond) - individual conditions for truthifying a fluent
%
%  This preciate enumerates the different ways in which the fluent F can become
%  true, which are collected by eps_p/4.
%
eps_p1((P & Q),A,E) :-
    eps_p(P,A,EP),
    eps_p(Q,A,EQ),
    E = (EP & EQ).
eps_p1((P & Q),A,E) :-
    eps_p(P,A,EP),
    eps_n(Q,A,EQn),
    E = (EP & Q & -EQn).
eps_p1((P & Q),A,E) :-
    eps_n(P,A,EPn),
    eps_p(Q,A,EQ),
    E = (P & -EPn & EQ).
eps_p1((P & Q),A,E) :-
    eps_p(P,A,EP),
    \+ eps_n(Q,A,_),
    E = (EP & Q).
eps_p1((P & Q),A,E) :-
    eps_p(Q,A,EQ),
    \+ eps_n(P,A,_),
    E = (P & EQ).

eps_p1((P | _),A,E) :-
    eps_p(P,A,E).
eps_p1((_ | Q),A,E) :-
    eps_p(Q,A,E).

eps_p1(-P,A,E) :-
    eps_n(P,A,E).

eps_p1(all(X,P),A,E) :-
    eps_p(P,A,EP),
    eps_n(P,A,EPn),
    E = all(X,(P & -EPn) | EP).
eps_p1(all(X,P),A,E) :-
    eps_p(P,A,EP),
    \+ eps_n(P,A,_),
    E = all(X,P | EP).

eps_p1(exists(X,P),A,E) :-
    eps_p(P,A,EP),
    E = exists(X,EP).

eps_p1(P,A,E) :-
    causes_true(P,A,E).

% eps_p1(B=C,A,false).   is implicit


%
%  eps_n1(+F,?Act,?Cond) - individual conditions for falsifying a fluent
%
%  This preciate enumerates the different ways in which the fluent F can become
%  false, which are collected by eps_n/4.
%
eps_n1((P & _),A,E) :-
    eps_n(P,A,E).
eps_n1((_ & Q),A,E) :-
    eps_n(Q,A,E).

eps_n1((P | Q),A,E) :-
    eps_n(P,A,EP),
    eps_n(Q,A,EQ),
    E = (EP & EQ).
eps_n1((P | Q),A,E) :-
    eps_n(P,A,EP),
    eps_p(Q,A,EQp),
    E = (EP & -Q & -EQp).
eps_n1((P | Q),A,E) :-
    eps_p(P,A,EPp),
    eps_n(Q,A,EQ),
    E = (-P & -EPp & EQ).
eps_n1((P | Q),A,E) :-
    eps_n(P,A,EP),
    \+ eps_p(Q,A,_),
    E = (EP & -Q).
eps_n1((P | Q),A,E) :-
    eps_n(Q,A,EQ),
    \+ eps_p(P,A,_),
    E = (-P & EQ).

eps_n1(-P,A,E) :-
    eps_p(P,A,E).

eps_n1(all(X,P),A,E) :-
    eps_n(P,A,EP),
    E = exists(X,EP).

eps_n1(exists(X,P),A,E) :-
    eps_n(P,A,EP),
    eps_p(P,A,EPp),
    E = all(X,(-P & -EPp) | EP).
eps_n1(exists(X,P),A,E) :-
    eps_n(P,A,EP),
    \+ eps_p(P,A,_),
    E = all(X,-P | EP).

eps_n1(P,A,E) :-
    causes_false(P,A,E).

% eps_n1(B=C,A,false).   is implicit


%
%  regression(+F,+A,-Fr) - Fr is the regression of F over action A
%
%  This predicate calculates the regression of a fluent F with respect to
%  an action A, yielding a new fluent Fr.  If A is free, will consider all
%  type of action that could affect the fluent.
%

%  If A is non-free, regression1 will succeed only once.
regression(F,A,Fr) :-
    nonvar(A),
    regression1(F,A,Fr).

%  If A is free, find all actions which could affect it.
regression(F,A,Fr) :-
    var(A),
    (bagof(Ft,B^regression_bagof(F,A,B,Ft),Fts) ->
        joinlist((|),Fts,Ftmp),
        simplify(Ftmp,Fr)
    ;
        Fr=F
    ).

regression_bagof(F,A,B,Ft) :-
    regression1(F,B,Ftp),
    (
      var(B), Ft=Ftp
    ;
      nonvar(B), Ft=(Ftp & (A=B))
    ).

regression1(F,A,Fr) :-
    eps_p(F,A,Ep),
    eps_n(F,A,En),
    simplify(Ep | (F & -En),Fr).
regression1(F,A,Fr) :-
    eps_p(F,A,Ep), 
    \+ eps_n(F,A,_),
    simplify(Ep | F,Fr).
regression1(F,A,Fr) :-
    eps_n(F,A,En), 
    \+ eps_p(F,A,_),
    simplify(F & -En,Fr).
regression1(F,A,Fr) :-
    \+ eps_n(F,A,_), 
    \+ eps_p(F,A,_),
    F = Fr.

%
%  holds(+F,+S) - fluent F holds in situation S
%
%  This predicate is true whenever the fluent F holds in situation S.
%
holds(true,_).
holds(A=B,_) :-     % no functional fluents, so equality does not vary
    A=B.
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
    %subs(V,_,F,F1), holds(F1,s0).
    holds(F,s0).
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
holds(-F,s0) :-
    prim_fluent(F),
    \+ initially(F).

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


