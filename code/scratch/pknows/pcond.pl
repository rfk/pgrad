
%
%  pcond_d1(F,C,P1)  -  depth 1 persistence condition for fluent F
%
%    The basic meaning of this pedicate is: if fluent F holds in situation
%    s, then it will continue to hold in all C-successors of s as long
%    as P1 is true in s.
% 
%    B is the 'background' for the query, the list of conjuncts already
%    known to persist.  F is the target and will be regressed.
%

pcond_d1(B,F,C,P1) :-
    ( bagof(Cn,pcond_d1_bagof(F,C,Cn),Cns) ->
        simplify_conjunction(Cns,SimpCns),
        joinlist((&),SimpCns,P1)
    ;
        P1=true
    ).

pcond_d1_bagof(F,C,Cn) :-
    action_with_vars(A,Vs),
    regression(F,A,R),
    adp_fluent(C,A,Ec),
    Cnt = !(Vs : (R | ~Ec)).

%
%  pcond(F,C,P)  -  persistence condition for F under C
%

pcond(F,C,P) :-
    (domain_falsehood(F) ->
        P = false
    ; domain_tautology(F) ->
        P = true
    ; 
        pcond_acc([F],C,P)
    ).

pcond_acc([F|Fs],C,P) :-
    pcond_d1(Fs,F,C,P1),
    length([F|Fs],Len), write('P'), write(Len), write('=  '), write(P1), nl,
    (domain_falsehood(P1) ->
        P = false
    ; domain_tautology(P1) ->
        joinlist('&',[F|Fs],P)
    ; 
      joinlist('&',[F|Fs],Ff),
      (domain_tautology(Ff=>P1) ->
        P = Ff
      ;
        pcond_acc([P1,F|Fs],C,P)
      )
    ).

