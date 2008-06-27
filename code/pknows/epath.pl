

regress_epath(P,C1,C2,POut) :-
  regress_epath_a(P,X,Pa),
  POut = (!(X^action) ; ?(X=C1) ; Pa ; ?(X=C2)).

regress_epath_a(A,X,P) :-
    atom(A), 
    adp_fluent(obs(A,Z),X,ObsDefn),
    adp_fluent(poss,X,PossDefn),
    P = (!(Z^observation) ; ?(ObsDefn) ; A ; !(X^action) ; ?(PossDefn) ; ?(ObsDefn)).
regress_epath_a(?(F),X,P) :-
    regression(F,X,Fr),
    P = ?(Fr).
regress_epath_a(!(Y^T),_,!(Y^T)).
regress_epath_a(P1 ; P2,X,P1a ; P2a) :-
    regress_epath_a(P1,X,P1a),
    regress_epath_a(P2,X,P2a).
regress_epath_a(P1 | P2,X,P1a | P2a) :-
    regress_epath_a(P1,X,P1a),
    regress_epath_a(P2,X,P2a).
regress_epath_a((P*),X,(Pa*)) :-
    regress_epath_a(P,X,Pa).

