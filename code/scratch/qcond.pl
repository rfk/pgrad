%
%  Determine constraint preconditions for formulae
%
%  Given a situation-suppressed formula  A, we aim to calculate a
%  situation-suppressed formulae Q*(A) such that:
%
%     Q*(A)[s] -->  forall(sp) s <= sp --> A
%
%  That is to say, is state s satisfies Q*(A), then it and all of its
%  legal successors will satisfy A.  Thus we aim to reason about state
%  constraints without needing induction.
%
%  We do this by defining a function Q(A) that is sufficient to ensure
%  that A holds in s and all its direct successors.  By finding a fixed
%  point for this function based on A, Q*(A) can be determined.
%

:- op(300,fx,~).
:- op(400,xfy,&).
:- op(500,xfy,v).

:- dynamic nextvar/1.

:- discontiguous eps_p/3, eps_n/3.

nextvar(1).

newvar(X) :-
    retract(nextvar(V)),
    V2 is V + 1,
    assert(nextvar(V2)),
    atom_codes(V,C1),
    atom_codes(v,Cv),
    append(Cv,C1,C2),
    atom_codes(X,C2), !.


to_leancop_form(P & Q,C) :-
    to_leancop_form(P,PC),
    to_leancop_form(Q,QC),
    C = ','(PC,QC), !.
to_leancop_form(P v Q,C) :-
    to_leancop_form(P,PC),
    to_leancop_form(Q,QC),
    C = ';'(PC,QC), !.
to_leancop_form(all(X,P),C) :-
    to_leancop_form(P,P2),
    subs(X,X1,P2,PC),
    C = all(X1:PC), !.
to_leancop_form(ex(X,P),C) :-
    to_leancop_form(P,P2),
    subs(X,X1,P2,PC),
    C = ex(X1:PC), !.
to_leancop_form(~P,C) :-
    to_leancop_form(P,PC),
    C = ~PC, !.
to_leancop_form(P,P).

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
        S=SP & SQ
    ), !.
simplify(P v Q,S) :-
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
        S=SP v SQ
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
simplify(all(X,P),S) :-
    simplify(P,SP),
    (
        SP=false, S=false
    ;
        SP=true, S=true
    ;
        S=all(X,SP)
    ), !.
simplify(ex(X,P),S) :-
    simplify(P,SP),
    (
        SP=false, S=false
    ;
        SP=true, S=true
    ;
        S=ex(X,SP)
    ), !.
simplify(P,P).

consequence(P1,P2) :-
    Fml = ~(true & ~false & P1) v P2,
    to_leancop_form(Fml,C),
    make_matrix(C,M),
    prove(M).


find_qcond([Qold|T],Q) :-
    length(T,Len), Len < 10,
    qcond_t(Qold,Qnew),
    write(Len), write(' :: '), write(Qnew), nl,
    (consequence(Qold,Qnew) ->
        joinlist(&,[Qold|T],Q)
    ; consequence(Qold,~Qnew) ->
        Q=false
    ;
        find_qcond([Qnew,Qold|T],Q)
    ).
find_qcond(P,Q) :-
    find_qcond([P],Q).
    

subs(_,_,T,Tr) :-
    var(T), Tr = T.
subs(X,Y,T,Tr) :-
    \+ var(T), T = X, Tr = Y.
subs(X,Y,T,Tr) :-
    T \= X, T =.. [F|Ts], sub_list(X,Y,Ts,Trs), Tr =.. [F|Trs].

sub_list(_,_,[],[]).
sub_list(X,Y,[T|Ts],[Tr|Trs]) :-
    subs(X,Y,T,Tr), sub_list(X,Y,Ts,Trs).

joinlist(_,[H],H).
joinlist(O,[H|T],J) :-
    T \= [],
    joinlist(O,T,TJ),
    J =.. [O,H,TJ].

qcond_t(P,Q) :-
    findall(Qt,A^qcond_t1(P,A,Qt),Qts),
    (
      Qts=[], Qtmp=true
    ;
      joinlist(&,Qts,Qp), Qtmp=Qp
    ),
    simplify(Qtmp,Q).

qcond_t(P,0,P).
qcond_t(P,N,Q) :-
     N > 0,
     N2 is N - 1,
     qcond_t(P,N2,Q2),
     qcond_t(Q2,Q).
    
% TODO: this doesnt handle quantification properly
%       Because the action appears outside quantifier scope.
%       need to rethink this a little for quantification
qcond_t1(P,A,Q) :-
    eps_n(P,A,QP),
    poss(A,QA),
    Qt = ~QA v ~QP,
    simplify(Qt,Q).

affected(P,A) :-
    eps_p(P,A,_) ; eps_n(P,A,_).

eps_p(P,A,E) :-
    setof(Et,eps_p1(P,A,Et),Ets),
    joinlist(v,Ets,E).
eps_n(P,A,E) :-
    setof(Et,eps_n1(P,A,Et),Ets),
    joinlist(v,Ets,E).

eps_p1(P & Q,A,E) :-
    eps_p(P,A,EP),
    eps_p(Q,A,EQ),
    E = EP & EQ.
eps_p1(P & Q,A,E) :-
    eps_p(P,A,EP),
    eps_n(Q,A,EQn),
    E = EP & Q & ~EQn.
eps_p1(P & Q,A,E) :-
    eps_n(P,A,EPn),
    eps_p(Q,A,EQ),
    E = P & ~EPn & EQ.
eps_p1(P & Q,A,E) :-
    eps_p(P,A,EP),
    \+ eps_n(Q,A,_),
    E = EP & Q.
eps_p1(P & Q,A,E) :-
    eps_p(Q,A,EQ),
    \+ eps_n(P,A,_),
    E = P & EQ.

eps_p1(P v _,A,E) :-
    eps_p(P,A,E).
eps_p1(_ v Q,A,E) :-
    eps_p(Q,A,E).

eps_p1(~P,A,E) :-
    eps_n(P,A,E).

eps_p1(all(X,P),A,E) :-
    eps_p(P,A,EP),
    eps_n(P,A,EPn),
    E = all(X,(P & ~EPn) v EP).
eps_p1(all(X,P),A,E) :-
    eps_p(P,A,EP),
    \+ eps_n(P,A,_),
    E = all(X,P v EP).

eps_p1(ex(X,P),A,E) :-
    eps_p(P,A,EP),
    E = ex(X,EP).


eps_n1(P & _,A,E) :-
    eps_n(P,A,E).
eps_n1(_ & Q,A,E) :-
    eps_n(Q,A,E).

eps_n1(P v Q,A,E) :-
    eps_n(P,A,EP),
    eps_n(Q,A,EQ),
    E = EP & EQ.
eps_n1(P v Q,A,E) :-
    eps_n(P,A,EP),
    eps_p(Q,A,EQp),
    E = EP & ~Q & ~EQp.
eps_n1(P v Q,A,E) :-
    eps_p(P,A,EPp),
    eps_n(Q,A,EQ),
    E = ~P & ~EPp & EQ.
eps_n1(P v Q,A,E) :-
    eps_n(P,A,EP),
    \+ eps_p(Q,A,_),
    E = EP & ~Q.
eps_n1(P & Q,A,E) :-
    eps_n(Q,A,EQ),
    \+ eps_p(P,A,_),
    E = ~P & EQ.

eps_n1(~P,A,E) :-
    eps_p(P,A,E).

eps_n1(all(X,P),A,E) :-
    eps_n(P,A,EP),
    E = ex(X,EP).

eps_n1(ex(X,P),A,E) :-
    eps_n(P,A,EP),
    eps_p(P,A,EPp),
    E = all(X,(~P & ~EPp) v EP).
eps_n1(ex(X,P),A,E) :-
    eps_n(P,A,EP),
    \+ eps_p(P,A,_),
    E = all(X,~P v EP).



%%%%%%%%%%%%%%%%%


eps_p(broken(X),drop(X),fragile(X)).
eps_n(broken(X),repair(X),true).

eps_p(holding(X),pickup(X),true).
eps_n(holding(X),drop(X),true).
eps_n(holding(X),putdown(X),true).

poss(drop(X),holding(X)).
poss(pickup(_),true).
poss(putdown(X),holding(X)).
poss(repair(X),holding(X) & hasglue).

getvars(A) :-
    A =.. [_|Args],
    maplist(newvar,Args).

