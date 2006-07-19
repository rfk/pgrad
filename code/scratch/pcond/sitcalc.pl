

action_term(pickup(_,_)).
action_term(putdown(_,_)).
action_term(drop(_,_)).

copy_action_term(A,At) :-
    A =.. [Af|Args],
    maplist(tovar,Args,VArgs),
    At =.. [Af|VArgs].

struct_equiv(P,Q) :-
    P==Q.
struct_equiv(A=B,C=D) :-
    A==D, B==C.
struct_equiv(P,Q) :-
    P =.. [F,P1,P2],
    Q =.. [F,Q1,Q2],
    member(F,['&','|','->','<->']),
    struct_equiv(P1,Q1),
    struct_equiv(P2,Q2).
struct_equiv(-P,-Q) :-
    struct_equiv(P,Q).
struct_equiv(all(X,P),all(Y,Q)) :-
    subs(Y,X,Q,Q2),
    struct_equiv(P,Q2).
struct_equiv(exists(X,P),exists(Y,Q)) :-
    subs(Y,X,Q,Q2),
    struct_equiv(P,Q2).

struct_oppos(P,Q) :-
    P = -P1, struct_equiv(P1,Q)
    ;
    Q = -Q1, struct_equiv(P,Q1).

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
        struct_equiv(SP,SQ), S=SP
    ;
        struct_oppos(SP,SQ), S=false
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
        struct_equiv(SP,SQ), S=SP
    ;
        struct_oppos(SP,SQ), S=true
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
%  consequence(+[Axioms],+Conc) - Fluent Conc is a consequence of the Axioms
%
%  This predicate employs full first-order reasoning to determine whether
%  the fluent expression Conc is logically entailed by the set of fluents
%  in Axioms.
%
consequence([],Conc) :-
    consequence([true],Conc), !.
consequence(F,Conc) :-
    F \= [_|_],
    consequence([F],Conc).
consequence(Axioms,Conc) :-
    % TODO: automatically unique names axioms?
    eprove([true,-false|Axioms],Conc,yes).


%fluent2term(F,N,N2) :-
%    var(F),
%    concat_atom([x,N],F),
%    N2 is N + 1.
%fluent2term(F,N,N) :-
%    ground(F).
%fluent2term(F,N,N2) :-
%    nonvar(F), \+ ground(F),
%    F =.. [_|Args],
%    fluent2term_list(Args,N,N2).
%
%fluent2term_list([],N,N).
%fluent2term_list([H|T],N,N2) :-
%    fluent2term(H,N,N3),
%    fluent2term_list(T,N3,N2).
    

%
%  joinlist(+Op,+In,-Out) - join items in a list using given operator
%
joinlist(O,[H|T],J) :-
    T \= [],
    joinlist(O,T,TJ),
    J =.. [O,H,TJ].
joinlist(_,[H],H).

%
%  eps_p(+F,?Act,?Cond) - conditions for a fluent becoming true
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made true by the action Act.
%
eps_p(P,A,E) :-
    bagof(Et,eps_p1(P,A,Et),Ets),
    joinlist((|),Ets,Etmp),
    simplify(Etmp,E).

%
%  eps_n(+F,?Act,?Cond) - conditions for a fluent becoming false
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made false by the action Act.
%
eps_n(P,A,E) :-
    bagof(Et,eps_n1(P,A,Et),Ets),
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
    subs(X,X1,P,P1),
    copy_action_term(A,At),
    eps_p(P1,At,EPt),
    eps_n(P1,At,EPnt),
    subs(X1,X2,At,A),
    ( At == A ->
        EP = EPt,
        EPn = EPnt
    ;
        EP = EPt & (X1=X2),
        EPn = EPnt & (X1=X2)
    ),
    E = all(X1,((P1 & -EPn) | EP)).
eps_p1(all(X,P),A,E) :-
    subs(X,X1,P,P1),
    copy_action_term(A,At),
    eps_p(P1,At,EPt),
    \+ eps_n(P1,At,_),
    subs(X1,X2,At,A),
    ( At == A ->
        EP = EPt
    ;
        EP = EPt & (X1=X2)
    ),
    E = all(X1,P1 | EP).

eps_p1(exists(X,P),A,E) :-
    subs(X,X1,P,P1),
    copy_action_term(A,At),
    eps_p(P1,At,EPt),
    subs(X1,X2,At,A),
    ( At == A ->
        EP = EPt
    ;
        EP = EPt & (X1=X2)
    ),
    E = exists(X1,EP).

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
    subs(X,X1,P,P1),
    copy_action_term(A,At),
    eps_n(P1,At,EPt),
    subs(X1,X2,At,A),
    ( At == A ->
        EP = EPt
    ;
        EP = EPt & (X1=X2)
    ),
    E = exists(X1,EP).

eps_n1(exists(X,P),A,E) :-
    subs(X,X1,P,P1),
    copy_action_term(A,At),
    eps_n(P1,At,EPt),
    eps_p(P1,At,EPpt),
    subs(X1,X2,At,A),
    ( At == A ->
        EP = EPt,
        EPp = EPpt
    ;
        EP = EPt & (X1=X2),
        EPp = EPpt & (X1=X2)
    ),
    E = all(X1,(-P1 & -EPp) | EP).
eps_n1(exists(X,P),A,E) :-
    subs(X,X1,P,P1),
    copy_action_term(A,At),
    eps_n(P1,At,EPt),
    \+ eps_p(P1,At,_),
    subs(X1,X2,At,A),
    ( At == A ->
        EP = EPt
    ;
        EP = EPt & (X1=X2)
    ),
    E = all(X1,-P1 | EP).

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
    regression1(F,A,Frt),
    simplify(Frt,Fr).

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
holds(-(A=B),_) :-
    A \= B.
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
subs(X,Y,T,Tr) :-
    T == X, Tr = Y.
subs(X,_,T,Tr) :-
    T \== X, var(T), T=Tr.
subs(X,Y,T,Tr) :-
    T \== X, nonvar(T), T =.. [F|Ts], subs_list(X,Y,Ts,Trs), Tr =.. [F|Trs].

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



knows(Agt,F,[]) :-
    pcond(F,legObs(Agt),P),
    holds(P,s0).
knows(Agt,F,[A|T]) :-
    pcond(F,legObs(Agt),P),
    regression(P,A,R),
    knows(agt,R,T).

