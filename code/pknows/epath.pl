%
%  epath.pl:  create and manipulate epistemic path terms.
%

%
%  enumerate_epath(E,En)  -  enumerate all possible values of each path 
%                            variable in the epath, reducing it from FODL
%                            to PDL (and hence making it decidable)
%
enumerate_epath(E,En) :-
    epath_vars(E,Vars),
    epath_vars_enum(Vars,VarVals),
    epath_elim_vars(E,VarVals,En).

%
%  epath_vars(E,Vars)  -  find all path variables (as opposed to formula-level
%                         variables) in the given epistemic path.
%
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

%
%  epath_vars_enum(VarsList,ValsList)  -  enumerate possible values for
%                                         each path variable.
%
%  The input is a list of typed variables (V:T), while the output is
%  a corresponding list of (V-N-Vals) with N the number of possible values
%  variable V can be given, and Vals the list of possible values.
%
epath_vars_enum([],[]).
epath_vars_enum([X:T|Vars],[X-N-Vals|VarVals]) :-
    findall(Val,call(T,Val),Vals),
    length(Vals,N),
    epath_vars_enum(Vars,VarVals).

%
%  epath_elim_vars(E,Vars,EOut)  -  eliminate variables from an epath
%
%  epath_elim_var(E,V-N-Vals,EOut)  -  elimate a single variable from an epath
%
%  Vars is a list of (V-N-Vals) triples as produced by epath_vars_enum.
%  The input epath E is converted in an equivalent path EOut but with
%  all vars in the list replaced by an enumeration of their values.
%
:- index(epath_elim_vars(0,1,0)).

epath_elim_vars(En,[],En).
epath_elim_vars(E,[X-N-Vals|VarVals],En) :-
    setof(En1,epath_elim_var(E,X-N-Vals,En1),En1s),
    joinlist('|',En1s,En2),
    epath_elim_vars(En2,VarVals,En).

epath_elim_var(E,X-N-Vals,En) :-
    numlist(1,N,Ns), member(N1,Ns), member(N2,Ns),
    epath_elim_var(E,X-N-Vals,N1,N2,En1),
    simplify_epath(En1,En).

% helper predicate for setof/3 call in epath_elim_var
epath_elim_var_seq_helper(E1 ; E2,VarVal,N1,N2,En1 ; En2) :-
    VarVal = _-N-_,
    numlist(1,N,Ns), member(Nt,Ns),
    epath_elim_var(E1,VarVal,N1,Nt,En1),
    epath_elim_var(E2,VarVal,Nt,N2,En2).

%
%  epath_elim_var(E,X-N-Vals,N1,N2,EOut)  -  eliminate variable X from path E
%
%  This predicate eliminates the variable X from the path E by enumerating
%  its possible values.  We assume that X is bound to Vals[N1] at the beginning
%  of the path, and ensure that X is bound to Vals[N2] at the end of the path.
%
%  See epath_elim_var/3 for how this is used - we basically enumerate all
%  possible pairs of N1 and N2 and union the resulting paths together.
%
%  The clauses are all straightforward except for the iteration operator,
%  which we handle using a Kleene-style construction inspired by the
%  paper "Logics of Communication and Change".
%
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
%  In the base case of K<=0, there can be no intermediate iterations of E.
%  In the recursive case, we can take any path with K<=K-1, or take any
%  path that results in binding K to Vals[K], then any path from Vals[K]
%  back to Vals[K], then any path from Vals[K] to Vals[N2].
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
%  simplify_epath  -  simplify an epistemic path
%
simplify_epath(X,_) :-
    var(X), !, fail.
simplify_epath(E1 ; E2,Es) :-
    simplify_epath(E1,E1s),
    simplify_epath(E2,E2s),
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
simplify_epath(E1 | E2,Es) :-
    simplify_epath(E1,E1s),
    simplify_epath(E2,E2s),
    ( E1s = ?(false) ->
        Es = E2s
    ; E2s = ?(false) ->
        Es = E1s
    ;  Es = (E1s | E2s)
    ), !.
simplify_epath(E*,Es) :-
    simplify_epath(E,E1s),
    ( E1s = ?(true) ->
        Es = ?(true)
    ; E1s = ?(false) ->
        Es = ?(false)
    ; E1s = ?(P) ->
        Es = ?(P)
    ;  Es = (E1s*)
    ), !.
simplify_epath(?(P),?(S)) :-
    simplify(P,S), !.
simplify_epath(!(X:T),!(X:T)).
simplify_epath(A,A) :-
    agent(A).


%
%  copy_epath(EIn,EOut)  -  copy an epath, renaming path variables
%
%  This produces a copy of EIn with all path variables replaced by
%  fresh variables.  All free formula variables remain unchanged.
%
copy_epath(E,Ec) :-
    epath_vars(E,EVarsT),
    maplist(arg(1),EVarsT,EVars),
    term_variables(E,TVars),
    vdelete_list(TVars,EVars,FVars),
    copy_term(E^FVars,E2^FVars2),
    FVars2=FVars,
    copy_epath_fmls(E2,Ec).

copy_epath_fmls(E1 ; E2,E1c ; E2c) :-
    copy_epath_fmls(E1,E1c),
    copy_epath_fmls(E2,E2c).
copy_epath_fmls(E1 | E2,E1c | E2c) :-
    copy_epath_fmls(E1,E1c),
    copy_epath_fmls(E2,E2c).
copy_epath_fmls(E*,Ec*) :-
    copy_epath_fmls(E,Ec).
copy_epath_fmls(?(P),?(Pc)) :-
    copy_fml(P,Pc).
copy_epath_fmls(!(V:T),!(V:T)).
copy_epath_fmls(A,A) :-
    agent(A).


%
%  pp_epath(E)  -  pretty-print an epistemic path
%
pp_epath_list([E],_,_,O1,D1) :-
    pp_epath(E,O1,D1).
pp_epath_list([E1,E2|Es],Op,D,O1,D1) :-
    pp_epath(E1,O1,D1), nl,
    pp_inset(D), write(Op), nl,
    pp_epath_list([E2|Es],Op,D,D1,D1).


pp_epath(E1 ; E2,O,D) :-
    flatten_op(';',[E1,E2],Es),
    D1 is D + 1,
    O1 is O + 1,
    pp_epath_list(Es,';',D,O1,D1).
pp_epath(E1 | E2,O,D) :-
    flatten_op('|',[E1,E2],Es),
    D1 is D + 1,
    O1 is O + 1,
    pp_epath_list(Es,'|',D,O1,D1).
pp_epath(?(P),O,D) :-
    D1 is D + 1,
    pp_inset(O), write('?  '),
    pp_fml(P,0,D1).
pp_epath(!(V:T),O,_) :-
    pp_inset(O), write('!  '), write(V:T).
pp_epath(E*,O,D) :-
    D1 is D + 1,
    pp_inset(O), write('*'), nl,
    pp_epath(E,D1,D1).
pp_epath(A,O,_) :-
    agent(A),
    pp_inset(O), write(A).

