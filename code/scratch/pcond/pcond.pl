
%
%  calc_p1(F,C,P1)  -  calculate P1 condition for fluent F under ADP C
%

calc_p1(F,C,P1) :-
    ( setof(Cn,A^calc_p1_setof(F,C,A,Cn),Cns) ->
        joinlist((&),Cns,P1tmp),
        simplify(P1tmp,P1)
    ;
        P1=true
    ).

calc_p1_setof(F,C,A,Cn) :-
    eps_n(F,A,En),
    adp_fluent(C,A,Ec),
    A =.. [_|Args],
    ex_multi(Args,(En & Ec),Cn1),
    Cn = -Cn1.

ex_multi([],F,F).
ex_multi([H|T],F,exists(H,E)) :-
    ex_multi(T,F,E).

calc_p(P,C,PC) :-
    calc_p1(P,C,F),
    calc_p_aux(P,0,C,F,PC,N),
    nl, write('Persistence Depth: '), write(N), nl.

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

