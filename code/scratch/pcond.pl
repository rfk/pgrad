%
%  Determine constraint preconditions for formulae
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

:- op(300,fx,~).
:- op(400,xfy,&).
:- op(500,xfy,v).

:- discontiguous eps_pd/3, eps_nd/3.

calc_p1(P,P1) :-
    ( setof(Cn,A^Cn1^(eps_n(P,A,Cn1), Cn = ~Cn1),Cns) ->
        joinlist((,),Cns,P1tmp),
        simplify(P1tmp,P1)
    ;
        P1=true
    ).

calc_p(P,PC) :-
    calc_p1(P,F),
    calc_p_aux(P,F,PC).

calc_p_aux(P,F,PC) :-
    ( consequence(P,F) ->
        ( consequence(P,false) ->
            PC = false
        ;
            PC=P
        )
    ;
        calc_p1(F,F1),
        calc_p_aux((P,F),F1,PC)
    ).


simplify((P,Q),S) :-
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
        S=(SP,SQ)
    ), !.
simplify((P;Q),S) :-
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
        S=(SP;SQ)
    ), !.
simplify(~P,S) :-
    simplify(P,SP),
    (
        SP=false, S=true
    ;
        SP=true, S=false
    ;
        SP = ~P2, S=P2
    ;
        S = ~SP
    ), !.
simplify(all(X:P),S) :-
    simplify(P,SP),
    (
        SP=false, S=false
    ;
        SP=true, S=true
    ;
        S=all(X:SP)
    ), !.
simplify(ex(X:P),S) :-
    simplify(P,SP),
    (
        SP=false, S=false
    ;
        SP=true, S=true
    ;
        S=ex(X:SP)
    ), !.
simplify(P,P).


consequence(P1,P2) :-
    Fml = ((true , ~false , P1) => P2),
    make_matrix(Fml,M),
    prove(M).


joinlist(_,[H],H).
joinlist(O,[H|T],J) :-
    T \= [],
    joinlist(O,T,TJ),
    J =.. [O,H,TJ].


eps_p(P,A,E) :-
    setof(Et,eps_p1(P,A,Et),Ets),
    joinlist(v,Ets,Etmp),
    simplify(Etmp,E).

eps_n(P,A,E) :-
    setof(Et,eps_n1(P,A,Et),Ets),
    joinlist(v,Ets,Etmp),
    simplify(Etmp,E).

eps_p1((P,Q),A,E) :-
    eps_p(P,A,EP),
    eps_p(Q,A,EQ),
    E = (EP,EQ).
eps_p1((P,Q),A,E) :-
    eps_p(P,A,EP),
    eps_n(Q,A,EQn),
    E = (EP,Q,~EQn).
eps_p1((P,Q),A,E) :-
    eps_n(P,A,EPn),
    eps_p(Q,A,EQ),
    E = (P,~EPn,EQ).
eps_p1((P,Q),A,E) :-
    eps_p(P,A,EP),
    \+ eps_n(Q,A,_),
    E = (EP,Q).
eps_p1((P,Q),A,E) :-
    eps_p(Q,A,EQ),
    \+ eps_n(P,A,_),
    E = (P,EQ).

eps_p1((P;_),A,E) :-
    eps_p(P,A,E).
eps_p1((_;Q),A,E) :-
    eps_p(Q,A,E).

eps_p1(~P,A,E) :-
    eps_n(P,A,E).

eps_p1(all(X:P),A,E) :-
    eps_p(P,A,EP),
    eps_n(P,A,EPn),
    E = all(X:((P,~EPn);EP)).
eps_p1(all(X:P),A,E) :-
    eps_p(P,A,EP),
    \+ eps_n(P,A,_),
    E = all(X:(P;EP)).

eps_p1(ex(X:P),A,E) :-
    eps_p(P,A,EP),
    E = ex(X:EP).

eps_p1(P,A,E) :-
    eps_pd(P,A,Et),
    alpha(A,Ea),
    E = (Ea,Et).


eps_n1((P,_),A,E) :-
    eps_n(P,A,E).
eps_n1((_,Q),A,E) :-
    eps_n(Q,A,E).

eps_n1((P;Q),A,E) :-
    eps_n(P,A,EP),
    eps_n(Q,A,EQ),
    E = (EP,EQ).
eps_n1((P;Q),A,E) :-
    eps_n(P,A,EP),
    eps_p(Q,A,EQp),
    E = (EP,~Q,~EQp).
eps_n1((P;Q),A,E) :-
    eps_p(P,A,EPp),
    eps_n(Q,A,EQ),
    E = (~P,~EPp,EQ).
eps_n1((P;Q),A,E) :-
    eps_n(P,A,EP),
    \+ eps_p(Q,A,_),
    E = (EP,~Q).
eps_n1((P;Q),A,E) :-
    eps_n(Q,A,EQ),
    \+ eps_p(P,A,_),
    E = (~P,EQ).

eps_n1(~P,A,E) :-
    eps_p(P,A,E).

eps_n1(all(X:P),A,E) :-
    eps_n(P,A,EP),
    E = ex(X:EP).

eps_n1(ex(X:P),A,E) :-
    eps_n(P,A,EP),
    eps_p(P,A,EPp),
    E = all(X:((~P , ~EPp) ; EP)).
eps_n1(ex(X:P),A,E) :-
    eps_n(P,A,EP),
    \+ eps_p(P,A,_),
    E = all(X:(~P , EP)).

eps_n1(P,A,E) :-
    eps_nd(P,A,Et),
    alpha(A,Ea),
    E = (Ea , Et).


%%%%%%%%%%%%%%%%%


eps_pd(broken(X),drop(X),fragile(X)).
eps_nd(broken(X),repair(X),true).

eps_pd(holding(X),pickup(X),true).
eps_nd(holding(X),drop(X),true).
eps_nd(holding(X),putdown(X),true).

alpha(drop(X),holding(X)).
alpha(pickup(_),true).
alpha(putdown(X),holding(X)).
alpha(repair(X),(holding(X) , hasglue)).

