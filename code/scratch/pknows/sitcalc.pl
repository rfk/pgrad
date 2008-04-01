
%
%  action_with_vars(A,Vs)  -  get an action term with variable arguments
%
%  This predicate binds A to an action term with all arguments set to
%  variables, and Vs to a matching variable list.
%
action_with_vars(A,Vs) :-
    prim_action(At),
    At =.. [F|ArgTypes],
    awv_collect(ArgTypes,Args,Vs),
    A =.. [F|Args].

awv_collect([],[],[]).
awv_collect([_|T],[Y|TA],[Y|TV]) :-
    awv_collect(T,TA,TV).


%
%  domain_axioms(Axs):  unify Axs with the set of domain axioms.
%
%  The domain axioms are the background theory against which entailment
%  queries should be posed using entails/2.
%

domain_axioms(Axs) :-
    ( retract(domain_axioms_cache(Axs)) ->
        assert(domain_axioms_cache(Axs))
    ;
        findall(C,constraint(C),Cs),
        joinlist('&',Cs,BgT),
        fml2axioms(BgT,Axs),
        assert(domain_axioms_cache(Axs))
    ).

constraint(true).
constraint(~false).


domain_falsehood(Fml) :-
    domain_axioms(Axs),
    entails(Axs,~Fml).
domain_tautology(Fml) :-
    domain_axioms(Axs),
    entails(Axs,Fml).


%
%  Define behavior of skolem fluents
%

skolem_fluent(F,Nm,Sit,Id,Args) :-
    F =.. [Nm,Sit,Id|Args],
    length(Args,Arity),
    concat_atom([skol,Arity],Nm).

func_fluent(F) :-
    skolem_fluent(F,_,_,_,_).

causes_value(F,A,X,(X=F2)) :-
    skolem_fluent(F,Nm,Sit,Id,Args),
    skolem_fluent(F2,Nm,do(A,Sit),Id,Args).

%
%  regression(+F,+A,-Fr) - Fr is the regression of F over action A
%
%  This predicate calculates the regression of a fluent F with respect to
%  an action A, yielding a new fluent Fr.  If A is free, will consider all
%  types of action that could affect the fluent.
%

%  If A is non-free, regression1 will succeed only once.
regression(F,A,Fr) :-
    nonvar(A), !,
    regression1(F,A,Frt),
    simplify_c(Frt,Fr).

%  If A is free, find all actions which could affect F.
regression(F,A,Fr) :-
    var(A),
    (bagof(Ft,B^regression_bagof(F,A,B,Ft),Fts) ->
        joinlist((|),Fts,Ftmp),
        simplify_c(Ftmp,Fr)
    ;
        Fr=F
    ).

regression_bagof(F,A,B,Ft) :-
    action_with_vars(B,_),
    regression1(F,B,Ftp),
    Ft=(Ftp & (A=B)).


regression1(F,A,Fr) :-
    is_atom(F), F \= (_ = _), F \= (_ \= _),
    ( extract_func_fluents(F,F2) ->
        regression1(F2,A,Fr)
    ;
        (causes_true(F,A,Ep) -> true ; Ep = false),
        (causes_false(F,A,En) -> true ; En = false),
        simplify_c(Ep | (F & ~En),Fr)
    ).
regression1(T1=T2,A,Fr) :-
   ( nonvar(T1), causes_value(T1,A,X1,C1) -> 
        ( nonvar(T2), causes_value(T2,A,X2,C2) ->
            simplify_c(?([X1,X2] : (C1 & C2 & (X1=X2))),Fr)
        ;
            simplify_c(?([X1] : (C1 & (X1=T2))),Fr)
        )
   ; nonvar(T2), causes_value(T2,A,X2,C2) ->
        simplify_c(?([X2] : (C2 & (T1=X2))),Fr)
   ;
        Fr = (T1=T2)
   ).
regression1(T1\=T2,A,Fr) :-
    regression1(~(T1=T2),A,Fr).
regression1(!(X : P),A,!(X : R)) :-
    regression1(P,A,R).
regression1(?(X : P),A,?(X : R)) :-
    regression1(P,A,R).
regression1(~P,A,~R) :-
    regression1(P,A,R).
regression1((P & Q),A,(R & S)) :-
    regression1(P,A,R),
    regression1(Q,A,S).
regression1((P | Q),A,(R | S)) :-
    regression1(P,A,R),
    regression1(Q,A,S).


%
%  extract_func_fluents(F,P)  -  extract function fluents from an atom
%
%  This predicate is used to re-write an atom that contains functional
%  fluents into a equivalent expression in which the functional fluents
%  are all applied to equality.
%
%  This in turn allows such expressions to actually be regressed.
%

extract_func_fluents(F,P) :-
    is_atom(F),
    F =.. [Pred|Args],
    extract_func_fluents_rec(Args,Vars,Eqs,Args2),
    % fail if we didnt extract anything
    Vars \= [], Eqs \= [],
    F2 =.. [Pred|Args2],
    joinlist('&',[F2|Eqs],Body),
    P = ?(Vars : Body).

% Use difference lists to build up list of Variables, Equality
% statements, and Predicate arguments to be used when extracting
% functional fluents.
%
extract_func_fluents_rec([],[],[],[]).
extract_func_fluents_rec([A|As],VSoFar,ESoFar,ASoFar) :-
    ( var(A) ->
        ASoFar = [A|ASF2],
        extract_func_fluents_rec(As,VSoFar,ESoFar,ASF2)
    ;
        ( is_func_fluent(A) ->
            ASoFar = [V|ASF2],
            VSoFar = [V|VSF2],
            ESoFar = [V=A|ESF2],
            extract_func_fluents_rec(As,VSF2,ESF2,ASF2)
        ;
            ASoFar = [A|ASF2],
            extract_func_fluents_rec(As,VSoFar,ESoFar,ASF2)
        )
    ).


%
%  Test whether a given term is a fluent or action
%
is_func_fluent(F) :-
    F =.. [Fn|Args],
    length(Args,N),
    length(TArgs,N),
    Ff =.. [Fn|TArgs],
    func_fluent(Ff).

is_prim_fluent(F) :-
    F =.. [Fn|Args],
    length(Args,N),
    length(TArgs,N),
    Ff =.. [Fn|TArgs],
    prim_fluent(Ff).

is_prim_action(A) :-
    A =.. [Fn|Args],
    length(Args,N),
    length(TArgs,N),
    Ff =.. [Fn|TArgs],
    prim_action(Ff).

%
%  holds(+F,+S) - fluent F holds in situation S
%
%  This predicate is true whenever the fluent F holds in situation S.
%
holds(true,_) :- !.
holds(A=B,_) :-     % no functional fluents, so equality does not vary
    A=B, !.
holds(~(A=B),_) :- 
    dif(A,B), !.
holds(F,do(A,S)) :-
    regression(F,A,Fr),
    holds(Fr,S).

holds(F1 => F2,s0) :-
    holds(~F1,s0) ; holds(F2,s0).
holds(F1 <=> F2,s0) :-
    holds(F1,s0) , holds(F2,s0)
    ;
    holds(~F1,s0) , holds(~F2,s0).
holds(F1 & F2,s0) :-
    holds(F1,s0), holds(F2,s0).
holds(F1 | F2,s0) :-
    holds(F1,s0) ; holds(F2,s0).
holds(!(V : F),s0) :-
    holds(~exists(V : ~F),s0).
holds(?([] : F),s0) :-
    holds(F,s0).
holds(?([V|T] : F),s0) :-
    subs(V,_,F,F1), holds(?(T : F1),s0).
holds(~(F1 => F2),s0) :- 
    holds((F1 & (~F2)),s0).
holds(~(F1 <=> F2),s0) :- 
    holds((F1 & (~F2) | ((~F1) & F2)),s0).
holds(~(F1 & F2),s0) :- 
    holds((~F1) | (~F2),s0).
holds(~(F1 | F2),s0) :-
    holds((~F1) & (~F2),s0).
holds(~!(V : F),s0) :-
    holds(?(V : F),s0).
holds(~?(V : F),s0) :-
    \+ holds(?(V : F),s0).
holds(F,s0) :-
    prim_fluent(Ft),
    functor(Ft,S,N), functor(F,S,N),
    initially(F).
holds(~F,s0) :-
    prim_fluent(Ft),
    functor(Ft,S,N), functor(F,S,N),
    \+ initially(F).


adp_fluent(pbu(Agt),A,C) :-
    adp_fluent(poss,A,C1),
    adp_fluent(canObs(Agt),A,C2),
    C = C1 & ~C2.

knows(Agt,F,[]) :-
    write('CALCULATING PERSISTENCE CONDITION:'), nl,
    pcond(F,pbu(Agt),P),
    write_latex(P), nl,
    write('CHECKING AGAINST D_S_0'), nl,
    (holds(P,s0) ->
        write('HOLDS'), nl
    ;   write('DOESNT HOLD'), nl, fail
    ), !.
knows(Agt,F,[A|T]) :-
    write('CALCULATING PERSISTENCE CONDITION:'), nl,
    pcond(F,pbu(Agt),P),
    write_latex(P),
    write('REGRESSING OVER '), write(A), write(':'), nl,
    regression(P,A,R),
    write('NEW QUERY: '), nl,
    adp_fluent(poss,A,Poss), adp_fluent(canObs(Agt),A,Obs),
    Q = (Poss & Obs) => R,
    write(knows(Agt,Q,T)), nl,
    knows(Agt,Q,T), !.


