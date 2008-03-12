

regress(F,X,r(F,X)).

regress_epath(P,C1,C2,POut) :-
  regress_epath_a(P,X,Pa),
  POut = (ex(X) ; t(X=C1) ; Pa ; t(X=C2)).

regress_epath_a(A,X,P) :-
    atom(A), 
    P = (ex(Z) ; t(obs(A,X)=Z) ; A ; ex(X) ; t(poss(X)) ; t(obs(A,X)=Z)).
regress_epath_a(t(F),X,P) :-
    regress(F,X,Fr),
    P = t(Fr).
regress_epath_a(ex(Y),_,ex(Y)).
regress_epath_a(P1 ; P2,X,P1a ; P2a) :-
    regress_epath_a(P1,X,P1a),
    regress_epath_a(P2,X,P2a).
regress_epath_a(P1 | P2,X,P1a | P2a) :-
    regress_epath_a(P1,X,P1a),
    regress_epath_a(P2,X,P2a).
regress_epath_a(i(P1),X,i(P1a)) :-
    regress_epath_a(P1,X,P1a).

