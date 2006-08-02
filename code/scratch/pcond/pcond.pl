
%
%  pcond_d1(F,C,P1)  -  depth 1 persistence condition for fluent F
%

pcond_d1(F,C,P1) :-
    ( bagof(Cn,pcond_d1_bagof(F,C,Cn),Cns) ->
        joinlist((&),Cns,P1tmp),
        simplify(P1tmp,P1)
    ;
        P1=true
    ).

pcond_d1_bagof(F,C,Cn) :-
    action_with_vars(A,Vs),
    eps_n(F,A,En),
    adp_fluent(C,A,Ec),
    Cnt = -exists(Vs,(En & Ec)),
    simplify(Cnt,Cn).

%
%  pcond(F,C,P)  -  persistence condition for F under C
%

pcond(F,C,P) :-
    % Don't waste time on falsehoods or tautologies
    ( consequence(F,false) ->
        P=false
    ; consequence([],F) ->
        P=true
    ;
        pcond_d1(F,C,Fp),
        pcond_aux([F],C,Fp,P)
    ).

pcond_aux(Fs,C,F,P) :-
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

