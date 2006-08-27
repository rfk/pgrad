
%
%  pcond_d1(F,C,P1)  -  depth 1 persistence condition for fluent F
%
%    The basic meaning of this pedicate is: if fluent F holds in situation
%    s, then it will continue to hold in all C-successors of s as long
%    as P1 is true in s.
%

%
%  Second attempt - special-case each operator to avoid redundancy
%  in the generated formulae.
%
pcond_d1v2(F1 & F2,C,P1 & P2) :-
    pcond_d1v2(F1,C,P1),
    pcond_d1v2(F2,C,P2), !.
pcond_d1v2(all(X,F),C,all(X,P1)) :-
    pcond_d1v2(F,C,P1), !.
pcond_d1v2(F1 | F2,C,P1) :-
    % TODO: think about this some more
    % Perhaps we can special-case for simple independence between F1/F2?
    pcond_d1(F1 | F2,C,P1).
pcond_d1v2(exists(X,F),C,P1) :-
    pcond_d1(exists(X,F),C,P1).
pcond_d1v2(-F,C,P1) :-
    pcond_d1(-F,C,P1).
    

%
%  first attempt - straightforward encoding of definition
%
pcond_d1(F,C,P1) :-
    ( bagof(Cn,pcond_d1_bagof(F,C,Cn),Cns) ->
        joinlist((&),Cns,P1tmp),
        simplify_c(P1tmp,P1)
    ;
        P1=true
    ).

pcond_d1_bagof(F,C,Cn) :-
    action_with_vars(A,Vs),
    eps_n(F,A,En),
    adp_fluent(C,A,Ec),
    Cnt = -exists(Vs,(En & Ec)),
    simplify_c(Cnt,Cn).

%
%  pcond(F,C,P)  -  persistence condition for F under C
%

pcond(F,C,P) :-
    % Don't waste time on falsehoods or tautologies
    domain_axioms(Axs),
    add_to_axioms(F,Axs,Axs2),
    ( entails(Axs2,false) ->
        P=false
    ; entails(Axs,F) ->
        P=true
    ;
        pcond_d1(F,C,Fp),
        pcond_aux(Axs2,C,[F],Fp,P)
    ).

pcond_aux(Axs,C,Fs,F,P) :-
    ( entails(Axs,F) ->
        ( entails(Axs,false) ->
            P = false
        ;
            joinlist('&',Fs,P)
        )
    ;
        pcond_d1(F,C,F1),
        add_to_axioms(F,Axs,Axs2),
        pcond_aux(Axs2,C,[F|Fs],F1,P)
   ).

pcondv2(F,C,P) :-
    % Don't waste time on falsehoods or tautologies
    domain_axioms(Axs),
    add_to_axioms(F,Axs,Axs2),
    ( entails(Axs2,false) ->
        P=false
    ; entails(Axs,F) ->
        P=true
    ;
        pcond_d1v2(F,C,Fp),
        pcondv2_aux(Axs2,C,[F],Fp,P)
    ).

pcondv2_aux(Axs,C,Fs,F,P) :-
    ( entails(Axs,F) ->
        ( entails(Axs,false) ->
            P = false
        ;
            joinlist('&',Fs,P)
        )
    ;
        pcond_d1v2(F,C,F1),
        add_to_axioms(F,Axs,Axs2),
        pcondv2_aux(Axs2,C,[F|Fs],F1,P)
   ).

