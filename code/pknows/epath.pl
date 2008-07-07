

regress_epath(P,C1,C2,POut) :-
  regress_epath_a(P,X,Pa),
  POut = (!(X:action) ; ?(X=C1) ; Pa ; ?(X=C2)).

regress_epath_a(A,X,P) :-
    atom(A), 
    adp_fluent(obs(A,Z),X,ObsDefn),
    adp_fluent(poss,X,PossDefn),
    P = (!(Z:observation) ; ?(ObsDefn) ; A ; !(X:action) ; ?(PossDefn) ; ?(ObsDefn)).
regress_epath_a(?(F),X,P) :-
    regression(F,X,Fr),
    P = ?(Fr).
regress_epath_a(!(Y:T),_,!(Y:T)).
regress_epath_a(P1 ; P2,X,P1a ; P2a) :-
    regress_epath_a(P1,X,P1a),
    regress_epath_a(P2,X,P2a).
regress_epath_a(P1 | P2,X,P1a | P2a) :-
    regress_epath_a(P1,X,P1a),
    regress_epath_a(P2,X,P2a).
regress_epath_a((P*),X,(Pa*)) :-
    regress_epath_a(P,X,Pa).


enumerate_epath(E,En) :-
    epath_vars(E,Vars),
    epath_vars_enum(Vars,VarVals),
    epath_elim_vars(E,VarVals,En).

epath_vars(E1 ; E2,Vars) :-
    epath_vars(E1,Vars1),
    epath_vars(E2,Vars2),
    epath_vars_union(Vars1,Vars2,Vars), !.
epath_vars(E1 | E2,Vars) :-
    epath_vars(E1,Vars1),
    epath_vars(E2,Vars2),
    epath_vars_union(Vars1,Vars2,Vars), !.
epath_vars(E*,Vars) :-
    epath_vars(E,Vars), !.
epath_vars(!(X:T),[X:T]) :- !.
epath_vars(?(_),[]) :- !.
epath_vars(A,[]) :-
    agent(A).

epath_vars_union([],Vars,Vars).
epath_vars_union([X:T|Vars1],Vars2,Vars) :-
    (ismember(X:T,Vars2) ->
        epath_vars_union(Vars1,Vars2,Vars)
    ;
        Vars = [X:T|VarsT],
        epath_vars_union(Vars1,Vars2,VarsT)
    ).

epath_vars_enum([],[]).
epath_vars_enum([X:T|Vars],[X-N-Vals|VarVals]) :-
    findall(Val,call(T,Val),Vals),
    length(Vals,N),
    epath_vars_enum(Vars,VarVals).

:- index(epath_elim_vars(0,1,0)).

epath_elim_vars(En,[],En).
epath_elim_vars(E,[X-N-Vals|VarVals],En) :-
    setof(En1,epath_elim_var(E,X-N-Vals,En1),En1s),
    joinlist('|',En1s,En2),
    epath_elim_vars(En2,VarVals,En).

epath_elim_var(E,X-N-Vals,En) :-
    numlist(1,N,Ns), member(N1,Ns), member(N2,Ns),
    epath_elim_var(E,X-N-Vals,N1,N2,En1),
    simplify_enum_epath(En1,En).

epath_elim_var_seq_helper(E1 ; E2,VarVal,N1,N2,En1 ; En2) :-
    VarVal = _-N-_,
    numlist(1,N,Ns), member(Nt,Ns),
    epath_elim_var(E1,VarVal,N1,Nt,En1),
    epath_elim_var(E2,VarVal,Nt,N2,En2).

epath_elim_var(E1 ; E2,VarVal,N1,N2,En) :-
    setof(EnT,epath_elim_var_seq_helper(E1 ; E2,VarVal,N1,N2,EnT),EnLst),
    joinlist('|',EnLst,En).
epath_elim_var(E1 | E2,VarVal,N1,N2,En) :-
    (epath_elim_var(E1,VarVal,N1,N2,En1) ->
        (epath_elim_var(E2,VarVal,N1,N2,En2) ->
            En = (En1 | En2)
        ;
            En = En1
        )
    ;
        epath_elim_var(E2,VarVal,N1,N2,En2)
    ).
epath_elim_var(E*,VarVal,N1,N2,En) :-
    VarVal = _-N-_,
    epath_elim_var_kln(E,VarVal,N1,N2,N,En).
epath_elim_var(!(X1:T1),X-_-_,N1,N2,En) :-
    (X1 == X ->
       En = (?(true))
    ;
       N1 = N2, En = (!(X1:T1))
    ).
epath_elim_var(?(P),X-_-Vals,N1,N2,?(Pn)) :-
    N1 = N2,
    nth1(N1,Vals,V), subs(X,V,P,Pn).
epath_elim_var(A,_,N1,N2,A) :-
    agent(A), N1=N2.


%
%  epath_elim_var_kln(E,VarVal,N1,N2,K,En)
%
%  Kleene-style elimination of variable from within E*
%
%  The idea here is that a world is reachable by path <En> whenever it is
%  reachable by iteration of path E, under the restriction that each iteration
%  of E ends with X bound to value number K or less.
%
%  Thus E* is equiv to En with K==length(Vals), but we build up the definition
%  recursively in order to eliminate variables.
%
% In the base case of K==0, there can be no intermediate iterations of E.
% In the recursive case, 
%
epath_elim_var_kln(E,VarVal,N1,N2,0,En) :-
    epath_elim_var(E,VarVal,N1,N2,En1),
    ( N1 = N2 ->
        En = ((?(true)) | En1)
    ;
        En = En1
    ).
epath_elim_var_kln(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1=K, N2=K,
    En = (EnK*),
    epath_elim_var_kln(E,VarVal,K,K,K1,EnK).
epath_elim_var_kln(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1=K, N2\=K,
    En = ((EnK*) ; EnFromK),
    epath_elim_var_kln(E,VarVal,K,K,K1,EnK),
    epath_elim_var_kln(E,VarVal,K,N2,K1,EnFromK).
epath_elim_var_kln(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1\=K, N2=K,
    En = (EnToK ; (EnK*)),
    epath_elim_var_kln(E,VarVal,K,K,K1,EnK),
    epath_elim_var_kln(E,VarVal,N1,K,K1,EnToK).
epath_elim_var_kln(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1\=K, N2\=K,
    En = (EnK1 | (EnToK ; (EnK*) ; EnFromK)),
    epath_elim_var_kln(E,VarVal,N1,N2,K1,EnK1),
    epath_elim_var_kln(E,VarVal,N1,K,K1,EnToK),
    epath_elim_var_kln(E,VarVal,K,K,K1,EnK),
    epath_elim_var_kln(E,VarVal,K,N2,K1,EnFromK).

%
%  simplify_enum_epath  -  simplify an enumerated epath
%
simplify_enum_epath(E1 ; E2,Es) :-
    simplify_enum_epath(E1,E1s),
    simplify_enum_epath(E2,E2s),
    ( E1s = ?(true) ->
        Es = E2s
    ; E1s = ?(false) ->
        Es = ?(false)
    ; E2s = ?(true) ->
        Es = E1s
    ; E2s = ?(false) ->
        Es = ?(false)
    ;  Es = (E1s ; E2s)
    ), !.
simplify_enum_epath(E1 | E2,Es) :-
    simplify_enum_epath(E1,E1s),
    simplify_enum_epath(E2,E2s),
    ( E1s = ?(false) ->
        Es = E2s
    ; E2s = ?(false) ->
        Es = E1s
    ;  Es = (E1s | E2s)
    ), !.
simplify_enum_epath(E*,Es) :-
    simplify_enum_epath(E,E1s),
    ( E1s = ?(true) ->
        Es = ?(true)
    ; E1s = ?(false) ->
        Es = ?(false)
    ; E1s = ?(P) ->
        Es = ?(P)
    ;  Es = (E1s*)
    ), !.
simplify_enum_epath(?(P),?(S)) :-
    simplify(P,S), !.
simplify_enum_epath(!(X:T),!(X:T)).
simplify_enum_epath(A,A) :-
    agent(A).


% TODO: copy epaths by renaming bound variables
copy_epath(E,E).
    
