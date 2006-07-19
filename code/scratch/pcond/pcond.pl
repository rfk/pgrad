
%
%  pcond_d1(F,C,P1)  -  depth 1 persistence condition for fluent F
%

pcond_d1(F,C,P1) :-
    ( setof(Cn,A^pcond_d1_setof(F,C,A,Cn),Cns) ->
        joinlist((&),Cns,P1tmp),
        simplify(P1tmp,P1)
    ;
        P1=true
    ).

pcond_d1_setof(F,C,A,Cn) :-
    eps_n(F,A,En),
    adp_fluent(C,A,Ec),
    free_vars(A,Vars),
    ex_multi(Vars,(En & Ec),Cn1),
    Cn = -Cn1.


free_vars(V,[V]) :-
    var(V).
free_vars(T,Vars) :-
    nonvar(T),
    T =.. [_|Args],
    maplist(free_vars,Args,VarsT),
    flatten(VarsT,Vars).

ex_multi([],F,F).
ex_multi([H|T],F,exists(H,E)) :-
    ex_multi(T,F,E).


%
%  pcond(F,C,P)  -  persistence condition for F under C
%

pcond(F,C,P) :-
    pcond_d1(F,C,Fp),
    pcond_aux([F],C,Fp,P).

pcond_aux(Fs,C,F,P) :-
    length(Fs,Depth),
    write('Up to depth: '), write(Depth), nl,
    ( consequence(Fs,F) ->
        ( consequence(Fs,false) ->
            P = false
        ;
            joinlist('&',Fs,P)
        )
    ;
        pcond_d1(F,C,F1),
        pcond_aux([F|Fs],C,F1,P)
   ).

