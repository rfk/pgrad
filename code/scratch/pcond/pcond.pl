
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
    action_term(A),
    eps_n(F,A,En),
    adp_fluent(C,A,Ec),
    free_vars(A,[],Vars),
    ex_multi(Vars,(En & Ec),Cn1),
    Cn = -Cn1.

free_vars(P,L) :-
    free_vars(P,[],L).

free_vars(V,Bound,Free) :-
    var(V),
    ( mymember(V,Bound) ->
        Free = []
    ;
        Free = [V]
    ), !.
free_vars(all(X,P),Bound,Free) :-
    append(X,Bound,Bound2),
    free_vars(P,Bound2,Free), !.
free_vars(exists(X,P),Bound,Free) :-
    append(X,Bound,Bound2),
    free_vars(P,Bound2,Free), !.
free_vars(T,Bound,Free) :-
    nonvar(T),
    T =.. [_|Args],
    free_vars_list(Args,Bound,[],Free).

free_vars_list([],_,L,L).
free_vars_list([H|T],Bound,Acc,L) :-
    free_vars(H,Bound,Acc2),
    append(Acc,Acc2,Acc3),
    free_vars_list(T,Bound,Acc3,Lt),
    sort(Lt,L).

mymember(_,[]) :- fail.
mymember(E,[H|T]) :-
    E == H
    ;
    mymember(E,T).

ex_multi([],F,F).
ex_multi([H|T],F,exists(H,E)) :-
    ex_multi(T,F,E).


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
    length(Fs,Depth),
    %write('Up to depth: '), write(Depth), write('...'), flush_output,
    ( consequence(Fs,F) ->
        ( consequence(Fs,false) ->
            P = false
        ;
            joinlist('&',Fs,P)
        )%, write('done'), nl
    ;
        %write('continuing'), nl,
        pcond_d1(F,C,F1),
        pcond_aux([F|Fs],C,F1,P)
   ).

