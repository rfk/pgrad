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
%  epath_elim_var/3 is det.
%

:- index(epath_elim_vars(0,1,0)).

epath_elim_vars(En,[],En).
epath_elim_vars(E,[X-N-Vals|VarVals],En) :-
    setof(En1,epath_elim_var(E,X-N-Vals,En1),En1s),
    epath_build('|',En1s,En2),
    epath_elim_vars(En2,VarVals,En).

epath_elim_var(E,X-N-Vals,En) :-
    numlist(1,N,Ns), member(N1,Ns), member(N2,Ns),
    epath_elim_var(E,X-N-Vals,N1,N2,En).

% helper predicate for setof/3 call in epath_elim_var
epath_elim_var_seq_helper(E1 ; E2,VarVal,N1,N2,En) :-
    VarVal = _-N-_,
    numlist(1,N,Ns), member(Nt,Ns),
    epath_elim_var(E1,VarVal,N1,Nt,En1),
    epath_elim_var(E2,VarVal,Nt,N2,En2),
    epath_build(';',[En1,En2],En).

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
%  epath_elim_var/5 is semidet
%
epath_elim_var(A,_,N,N,A) :-
    agent(A).
epath_elim_var(E1 ; E2,VarVal,N1,N2,En) :-
    setof(EnT,epath_elim_var_seq_helper(E1 ; E2,VarVal,N1,N2,EnT),EnLst),
    epath_build('|',EnLst,En).
epath_elim_var(E1 | E2,VarVal,N1,N2,En) :-
    (epath_elim_var(E1,VarVal,N1,N2,En1) ->
        (epath_elim_var(E2,VarVal,N1,N2,En2) ->
            epath_build('|',[En1,En2],En)
        ;
            En = En1
        )
    ;
        epath_elim_var(E2,VarVal,N1,N2,En2),
        En = En2
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
epath_elim_var(?(P),X-_-Vals,N,N,?(Pn)) :-
    nth1(N,Vals,V), subs(X,V,P,PnT),
    simplify(PnT,Pn), Pn \= ?(false).


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
%  We memoize the results since the recursive definition repeats lots and
%  lots of calculations.
%
%  epath_elim_var_kln/6 is semidet.
%

:- dynamic(epath_kln_memo_mode/1).
:- dynamic(epath_kln_memo/6).
:- index(epath_kln_memo(1,0,1,1,1,0)).

epath_kln_memo_mode(none).
epath_kln_set_memo_mode(M) :-
    retract(epath_kln_memo_mode(_)),
    assert(epath_kln_memo_mode(M)).

epath_elim_var_kln(E,VarVal,N1,N2,K,En) :-
    epath_kln_memo_mode(Mode),
    ( Mode=basic ->
        ( epath_kln_memo(E,VarVal,N1,N2,K,En) ->
            true
        ;
            epath_elim_var_kln_(E,VarVal,N1,N2,K,En),
            assert(epath_kln_memo(E,VarVal,N1,N2,K,En))
        )
    ; Mode=none ->
        epath_elim_var_kln_(E,VarVal,N1,N2,K,En)
    ;
      throw(epath_kln_memo_mode(Mode))
    ).

%
%  actual implementation of epath_elim_var_kln
%  all four clauses are mutually exclusive so we use cut at
%  the earliest possible moment.
%

epath_elim_var_kln_(E,VarVal,N1,N2,0,En) :-
    !,
    epath_elim_var(E,VarVal,N1,N2,En1),
    ( N1 = N2 ->
        epath_build('|',[(?(true)),En1],En)
    ;
        En = En1
    ).
epath_elim_var_kln_(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1=K, N2=K,
    !,
    epath_elim_var_kln(E,VarVal,K,K,K1,EnK),
    epath_build('*',EnK,En).
epath_elim_var_kln_(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1=K, N2\=K,
    !,
    epath_elim_var_kln(E,VarVal,K,N2,K1,EnFromK),
    (epath_elim_var_kln(E,VarVal,K,K,K1,EnK) ->
        epath_build('*',EnK,EnKS),
        epath_build(';',[EnKS,EnFromK],En)
    ;
        En = EnFromK
    ).
epath_elim_var_kln_(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1\=K, N2=K,
    !,
    epath_elim_var_kln(E,VarVal,N1,K,K1,EnToK),
    (epath_elim_var_kln(E,VarVal,K,K,K1,EnK) ->
        epath_build('*',EnK,EnKS),
        epath_build(';',[EnToK,EnKS],En)
    ;
        En = EnToK
    ).
epath_elim_var_kln_(E,VarVal,N1,N2,K,En) :-
    K > 0, K1 is K - 1, N1\=K, N2\=K,
    !,
    ( epath_elim_var_kln(E,VarVal,N1,N2,K1,EnK1) ->
        ( (epath_elim_var_kln(E,VarVal,N1,K,K1,EnToK),
         epath_elim_var_kln(E,VarVal,K,N2,K1,EnFromK)) ->
            ( epath_elim_var_kln(E,VarVal,K,K,K1,EnK) ->
                epath_build('*',EnK,EnKS),
                epath_build(';',[EnToK,EnKS,EnFromK],En1),
                epath_build('|',[EnK1,En1],En)
            ;
                epath_build(';',[EnToK,EnFromK],En1),
                epath_build('|',[EnK1,En1],En)
            )
        ;
            En = EnK1
        )
    ;
        epath_elim_var_kln(E,VarVal,N1,K,K1,EnToK),
        epath_elim_var_kln(E,VarVal,K,N2,K1,EnFromK),
        ( epath_elim_var_kln(E,VarVal,K,K,K1,EnK) ->
            epath_build('*',EnK,EnKS),
            epath_build(';',[EnToK,EnKS,EnFromK],En)
        ;
            epath_build(';',[EnToK,EnFromK],En)
        )
    ).
    

%
%  epath_build(Op,Args,EPath)  -  build an epath, with simplification
%
%  This predicate builds an epath, applying simplifications appropriate
%  to the top-level operator but assuming all argument paths are already
%  simplified.
%

epath_build_off('|',Es,E) :-
    ( Es = [] ->
        E = ?false
    ;
        joinlist('|',Es,E)
    ), !.
epath_build_off(';',Es,E) :-
    ( Es = [] ->
        E = ?false
    ;
        joinlist(';',Es,E)
    ), !.
epath_build_off('*',E,E*) :- !.

epath_build('|',Es,E) :-
    flatten_op('|',Es,Es0),
    partition('='(?false),Es0,_,Es1),
    simplify_epath_choice_subsumes(Es1,Es2),
    simplify_epath_choice_union(Es2,Es3),
    ( Es3 = [] ->
        E = (?false)
    ;
        joinlist('|',Es3,E)
    ).

epath_build(';',Es,E) :-
    flatten_op(';',Es,Es0),
    ( member(?false,Es0) -> 
        E = (?false)
    ;
        partition('='(?true),Es0,_,Es1),
        ( Es1 = [] ->
            E = (?true)
        ;
            simplify_epath_seq_combine(Es1,Ss),
            joinlist(';',Ss,E)
        )
    ).

epath_build('*',E,Eb) :-
    simplify_star_contents(E,E1),
    ( E1 = (?(P)) ->
        Eb = (?(P))
    ;
        Eb = (E1*)
    ).


%
%  simplify_epath  -  simplify an epistemic path
%
%  we can do this by recursively stripping off the outermost operator,
%  simplifying the argument paths, then apply epath_build.
%
simplify_epath(X,_) :-
    var(X), !, throw(cant_simplify_a_free_epath).
simplify_epath(A,A) :-
    agent(A).
simplify_epath(E1 ; E2,Es) :-
    flatten_op(';',[E1,E2],Eseq),
    maplist(simplify_epath,Eseq,Esimp),
    epath_build(';',Esimp,Es).
simplify_epath(E1 | E2,Es) :-
    flatten_op('|',[E1,E2],Eseq),
    maplist(simplify_epath,Eseq,Esimp),
    epath_build('|',Esimp,Es).
simplify_epath(E*,Es) :-
    simplify_epath(E,E1s),
    epath_build('*',E1s,Es).
simplify_epath(?(P),?(S)) :-
    simplify(P,S).
simplify_epath(!(X:T),!(X:T)).


%
%  Simplification for operations within a star.
%
simplify_star_contents(E1,E2) :-
    ( simplify_star_contents1(E1,Es) ->
        simplify_star_contents(Es,E2)
    ;
        E2 = E1
    ).

simplify_star_contents1(E*,E).

% Any choices within a star that are simply ?true can be removed,
% as we always have the option of staying in current state.
simplify_star_contents1(E1 | E2,Ep) :-
    flatten_op('|',[E1,E2],Es),
    partition('='(?true),Es,Ts,Es2),
    length(Ts,N), N > 0,
    joinlist('|',Es2,Ep).
%
%  Flatten stars in (B1* | (B2* | B3*)*)* 
simplify_star_contents1(E,Ep) :-
    ( E = ((B1*) | (((B2*) | (B3*))*)) ; E = ((((B1*) | (B2*))*) | (B3*)) ) ->
    Ep = ((B1*) | (B2*) | (B3*)).

%
%  Remove choices that are subsumed by repetition of another branch
simplify_star_contents1(E1 | E2,Ep) :-
    flatten_op('|',[E1,E2],Es),
    simplify_epath_star_subsumes(Es,Ss),
    joinlist('|',Ss,Ep).

simplify_epath_star_subsumes(Es,Ss) :-
    simplify_epath_star_subsumes(Es,[],0,Ss).
 
simplify_epath_star_subsumes([],Acc,1,Acc).
simplify_epath_star_subsumes([E|Es],Acc,HaveSimpd,Ss) :-
    ( member(E2,Acc), epath_subsumes(E2*,E) ->
        simplify_epath_star_subsumes(Es,Acc,1,Ss)
    ;
        partition(epath_subsumes(E*),Acc,Rem,Acc2),
        ( Rem = [] -> NewHaveSimpd = HaveSimpd ; NewHaveSimpd = 1 ),
        simplify_epath_star_subsumes(Es,[E|Acc2],NewHaveSimpd,Ss)
    ).



%
%  simplify branches in a choice by removing any subsumed by another branch
%
simplify_epath_choice_subsumes(Es,Ss) :-
    simplify_epath_choice_subsumes(Es,[],Ss).
 
simplify_epath_choice_subsumes([],Acc,Acc).
simplify_epath_choice_subsumes([E|Es],Acc,Ss) :-
    ( member(E2,Acc), epath_subsumes(E2,E) ->
        simplify_epath_choice_subsumes(Es,Acc,Ss)
    ;
        partition(epath_subsumes(E),Acc,_,Acc2),
        simplify_epath_choice_subsumes(Es,[E|Acc2],Ss)
    ).

%
%  simplify branches in a choice by combining two branches into a single,
%  simpler branch giving their union.
%
simplify_epath_choice_union(Es,Ss) :-
    simplify_epath_choice_union(Es,[],Ss).

simplify_epath_choice_union([],Acc,Acc).
simplify_epath_choice_union([E|Es],Acc,Ss) :-
    ( (select(E1,Acc,Rest), simplify_epath_union(E,E1,Eu)) ->
        simplify_epath_choice_union([Eu|Es],Rest,Ss)
    ;
        simplify_epath_choice_union(Es,[E|Acc],Ss)
    ).


%
%  simplify_epath_seq_combine(Es,Ss)  -  simplify sequence of paths by
%                                        combining adjacent ones.
%
simplify_epath_seq_combine(Es,Ss) :-
    simplify_epath_seq_combine(Es,[],Ss).

simplify_epath_seq_combine([E],Acc,Ss) :-
    reverse([E|Acc],Ss).
simplify_epath_seq_combine([E|Es],Acc,Ss) :-
    ( simplify_epath_combine([E|Es],Es2) ->
        simplify_epath_seq_combine_recheck(Es2,Acc,Ss)
    ;
      simplify_epath_seq_combine(Es,[E|Acc],Ss)
    ).

:- index(simplify_eapth_seq_combine_recheck(0,1,0)).

simplify_epath_seq_combine_recheck(Es,[],Ss) :-
    simplify_epath_seq_combine(Es,[],Ss).
simplify_epath_seq_combine_recheck(Es,[A|Acc],Ss) :-
    ( simplify_epath_combine([A|Es],Es2) ->
        simplify_epath_seq_combine_recheck(Es2,Acc,Ss)
    ;
      simplify_epath_seq_combine(Es,[A|Acc],Ss)
    ).

%
%  epath_subsumes(E1,E2)  -  detect common cases where one epath completely
%                            subsumes another.  That is, all worlds reachable
%                            by path E2 are also reachable by path E1.
%
%  epath_subsumes/2 is det, which we ensure using cuts
%
epath_subsumes(E,E) :- !.
epath_subsumes(E*,E1*) :-
    epath_subsumes(E*,E1), !.
epath_subsumes(E*,E1) :-
    epath_subsumes(E,E1), !.
epath_subsumes(E*,E1) :-
    epath_seq_split(E1,[P1,P2],[]),
    epath_subsumes(E*,P1),
    epath_subsumes(E*,P2), !.
epath_subsumes(E,E1 | E2) :-
    epath_subsumes(E,E1),
    epath_subsumes(E,E2), !.
epath_subsumes(E1 | E2,E) :-
    (epath_subsumes(E1,E) ; epath_subsumes(E2,E)), !.
epath_subsumes(E1 ; E2,E) :-
    epath_seq_split(E,[P1,P2],[]),
    epath_subsumes(E1,P1),
    epath_subsumes(E2,P2), !.

%
%  simplify_epath_union(E1,E2,Eu)  -  simplify E1 and E2 into their union
%                                     (E1 | E2) <=> Eu
%
%  simplify_epath_combine(Es,Esc)  -    simplify E1;E2;P into Ec;P
%
%  This basically allows us to special-case a number of common forms.
%
simplify_epath_union(E1,E2,Eu) :-
    simplify_epath_union1(E1,E2,Eu)
    ;
    simplify_epath_union1(E2,E1,Eu).

%  P1 | (P1 ; P2* ; P2)   =>   P1 ; P2*
simplify_epath_union1(E1,E2,Eu) :-
    P1 = E1,
    epath_seq_split(E2,[P1,P2*,P2],[]),
    epath_build('*',P2,P2S),
    epath_build(';',[P1,P2S],Eu).
%  P1 | (P2 ; P2* ; P1)   =>   P2* ; P1
simplify_epath_union1(E1,E2,Eu) :-
    P1 = E1,
    epath_seq_split(E2,[P2,P2*,P1],[]),
    epath_build('*',P2,P2S),
    epath_build(';',[P2S,P1],Eu).
%  P1 | (P2* ; P2 ; P1)   =>   P2* ; P1
simplify_epath_union1(E1,E2,Eu) :-
    P1 = E1,
    epath_seq_split(E2,[P2*,P2,P1],[]),
    epath_build('*',P2,P2S),
    epath_build(';',[P2S,P1],Eu).
% ?P1 | ?P2   =>   ?(P1 | P2)
simplify_epath_union1(?P1,?P2,?Pu) :-
    fml2cnf(P1 | P2,Pu1),
    simplify(Pu1,Pu).


% P1* ; (P2 ; (P1*))*   =>   (P1* | P2*)*
simplify_epath_combine(E,[Ec|Rest]) :-
    epath_seq_split(E,[P1*,Pr*],Rest),
    epath_seq_split(Pr,[P2,P1*],[]),
    epath_build('|',[P1*,P2*],Ec1),
    epath_build('*',Ec1,Ec).
% (P1* ; P2)* ; P1*   =>   (P1* | P2*)*
simplify_epath_combine(E,[Ec|Rest]) :-
    epath_seq_split(E,[Pr*,P1*],Rest),
    epath_seq_split(Pr,[P1*,P2],[]),
    epath_build('|',[P1,P2],Ec1),
    epath_build('*',Ec1,Ec).
% (P1* ; P2)* ; P1 ; P1*   =>   (P1* | P2*)*
simplify_epath_combine(E,[Ec|Rest]) :-
    epath_seq_split(E,[Pr*,P1,P1*],Rest),
    epath_seq_split(Pr,[P1*,P2],[]),
    epath_build('|',[P1,P2],Ec1),
    epath_build('*',Ec1,Ec).
% P1* ; P2*   =>   P1*   if P1 > P2
simplify_epath_combine(E,[Ec|Rest]) :-
    epath_seq_split(E,[P1*,P2*],Rest),
    ( epath_subsumes(P1,P2), Ec = P1
    ; epath_subsumes(P2,P1), Ec = P2
    ).
% ?P1 ; ?P2   =>   ?(P1 & P2)
simplify_epath_combine(E,[?(Pc)|Rest]) :-
    epath_seq_split(E,[?P1,?P2],Rest),
    fml2cnf(P1 & P2,Pc1),
    simplify(Pc1,Pc).


:- index(epath_seq_split(1,1,0)).

epath_seq_split(E1 ; E2,Seqs,Rest) :-
    flatten_op(';',[E1,E2],Es),
    epath_seq_split_prep(Seqs,Preps),
    epath_seq_split(Es,Preps,Rest),
    epath_seq_split_unprep(Preps,Seqs).

epath_seq_split([E|Es],Seqs,Rest) :-
    epath_seq_split([E|Es],[],Seqs,Rest).

epath_seq_split(Rest,[],[],Rest).
epath_seq_split(Rest,[S-Vs|Todo],[],Rest) :-
    reverse(Vs,VsR),
    ( var(S) ->
        S = VsR
    ;
        joinlist(';',VsR,S)
    ),
    epath_seq_split(Rest,Todo,[],Rest).
epath_seq_split([E|Es],Todo,[S|Seqs],Rest) :-
    ( var(S) ->
        ((Todo = [S2-Vs|Todo2], S2 == S) ->
            (epath_seq_split([E|Es],Todo,Seqs,Rest)
            ;
            epath_seq_split(Es,[S-[E|Vs]|Todo2],[S|Seqs],Rest))
        ;
            epath_seq_split(Es,[S-[E]|Todo],[S|Seqs],Rest)
        )
    ;
      epath_seq_split_unify(S,[E|Es],Es2), epath_seq_split(Es2,Todo,Seqs,Rest)
    ).
epath_seq_split([],Todo,[S],Rest) :-
    var(S), Todo = [S2-_|_], S2 == S, 
    epath_seq_split([],Todo,[],Rest).


epath_seq_split_unify(P,[E|Es],Es) :-
    var(P), P=E, !.
epath_seq_split_unify(P1 ; P2,Es,Es2) :-
    epath_seq_split_unify(P1,Es,Es1),
    epath_seq_split_unify(P2,Es1,Es2), !.
epath_seq_split_unify(E,[E|Es],Es).

epath_seq_split_prep([],[]).
epath_seq_split_prep([S|Seqs],[P|Preps]) :-
    (var(S) -> true ; S=P ),
    epath_seq_split_prep(Seqs,Preps).
epath_seq_split_unprep([],[]).
epath_seq_split_unprep([P|Preps],[S|Seqs]) :-
    ( P = [_|_] -> joinlist(';',P,S) ; P=S ),
    epath_seq_split_unprep(Preps,Seqs).

    

%
%  copy_epath(EIn,EOut)  -  copy an epath, renaming path variables
%
%  This produces a copy of EIn with all path variables replaced by
%  fresh variables.  All free formula variables remain unchanged, while
%  all bound formula variables are also renamed.
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

pp_epath(E) :-
    pp_epath(E,0,0).

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



:- begin_tests(epath,[sto(rational_trees)]).

test(enum1) :-
    enumerate_epath(!(X:location) ; ?test(X),E),
    E = (?(test(c) | test(d))), !.

test(enum2) :-
    enumerate_epath(!(X:location) ; ((ann ; !(X:location))*),E),
    E = (ann*), !.

test(enum3) :-
    enumerate_epath(!(X:location) ; (((ann | bob) ; !(X:location))*),E),
    E =((ann | bob)*), !.

test(enum4) :-
    enumerate_epath(!(X:location) ; ((ann ; ?test1(X) ; !(X:location))*),E),
    E = (((ann ; ?test1(c))* | (ann ; ?test1(d))*)*), !.


:- end_tests(epath).
