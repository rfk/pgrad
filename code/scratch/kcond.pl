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

:- dynamic nextvar/1.
nextvar(1).

newvar(X) :-
    retract(nextvar(V)),
    V2 is V + 1,
    assert(nextvar(V2)),
    atom_codes(V,C1),
    atom_codes(a,Ca),
    append(Ca,C1,C2),
    atom_codes(X,C2).

ssa(broken(X),A,A=drop(X),A=repair(X)).

cfluent(poss(repair(X)),holding(X)).
cfluent(poss(drop(X)),holding(X)).

kcond(and(A,B),X) :-
    kcond(A,XA),
    kcond(B,XB),
    X = and(XA,XB).

kcond(not(F),X) :-
    ssa(F,A,Fp,Fn),
    newvar(A),
    X = and(not(F),forall(A,or(not(poss(A)),not(Fp),Fn))).

kcond(F,X) :-
    ssa(F,A,Fp,Fn),
    newvar(A),
    X = and(F,forall(A,or(not(Poss(A)),Fp,not(Fn)))).

