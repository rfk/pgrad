%
%  Determine persistence conditions for formulae
%
%  Given a situation-suppressed formula  A, we aim to calculate a
%  situation-suppressed formulae P(A) such that:
%
%     P(A)[s] <->  forall(sp) s <= sp -> A
%
%  That is to say, if state s satisfies P(A), then it and all of its
%  legal successors will satisfy A.  Thus we aim to reason about state
%  constraints without needing induction.
%
%  We do this by defining a function P1(A) that is sufficient to ensure
%  that A holds in s and all its direct successors.  By finding a fixed
%  point for this function based on A, P(A) can be determined.
%

:- [pred].

calc_p1(P,C,P1) :-
    ( setof(Cn,A^Cn1^(eps_n(P,C,A,Cn1), Cn = -Cn1),Cns) ->
        joinlist((&),Cns,P1tmp),
        simplify(P1tmp,P1)
    ;
        P1=true
    ).

calc_p(P,C,PC) :-
    calc_p1(P,C,F),
    calc_p_aux(P,0,C,F,PC,N),
    write(N), nl.

calc_p_aux(P,N0,C,F,PC,N) :-
    ( consequence(P,F) ->
        ( consequence(P,false) ->
            PC = false
        ;
            PC=P
        ), N=N0
    ;
        calc_p1(F,C,F1),
        N1 is N0 + 1,
        calc_p_aux((P & F),N1,C,F1,PC,N)
    ).


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


consequence(P1,P2) :-
    Fml = ((true & -false & P1) -> P2),
    tautology(Fml).


joinlist(_,[H],H).
joinlist(O,[H|T],J) :-
    T \= [],
    joinlist(O,T,TJ),
    J =.. [O,H,TJ].


eps_p(P,C,A,E) :-
    setof(Et,eps_p1(P,C,A,Et),Ets),
    joinlist((|),Ets,Etmp),
    simplify(Etmp,E).

eps_n(P,C,A,E) :-
    setof(Et,eps_n1(P,C,A,Et),Ets),
    joinlist((|),Ets,Etmp),
    simplify(Etmp,E).

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
    eps_p(P,C,A,EP),
    eps_n(P,C,A,EPn),
    E = all(X,((P & -EPn) | EP)).
eps_p1(all(X,P),C,A,E) :-
    eps_p(P,C,A,EP),
    \+ eps_n(P,C,A,_),
    E = all(X,(P | EP)).

eps_p1(exists(X,P),C,A,E) :-
    eps_p(P,C,A,EP),
    E = exists(X,EP).

eps_p1(P,C,A,E) :-
    % construct eps_p for basic fluent
    eps_pd(P,A,Et),
    % look up conditions from C
    alpha(A,Ea),
    E = (Ea & Et).


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
    eps_n(P,C,A,EP),
    E = exists(X,EP).

eps_n1(exists(X,P),C,A,E) :-
    eps_n(P,C,A,EP),
    eps_p(P,C,A,EPp),
    E = all(X,((-P & -EPp) | EP)).
eps_n1(exists(X,P),C,A,E) :-
    eps_n(P,C,A,EP),
    \+ eps_p(P,C,A,_),
    E = all(X,(-P | EP)).

eps_n1(P,C,A,E) :-
    % construct eps_n for basic fluent
    eps_nd(P,A,Et),
    % construct conditions from C
    alpha(A,Ea),
    E = (Ea & Et).


%%%%%%%%%%%%%%%%%


eps_pd(broken(X),drop(X),fragile(X)).
eps_nd(broken(X),repair(X),true).

eps_pd(holding(X),pickup(X),true).
eps_nd(holding(X),drop(X),true).
eps_nd(holding(X),putdown(X),true).

alpha(drop(X),holding(X)).
alpha(pickup(_),true).
alpha(putdown(X),holding(X)).
alpha(repair(X),(holding(X) & hasglue)).

