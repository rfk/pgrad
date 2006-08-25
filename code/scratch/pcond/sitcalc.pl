
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
awv_collect([D|T],[Y|TA],[Y:D|TV]) :-
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
constraint(-false).

%
%  eps_p(+F,?Act,?Cond) - conditions for a fluent becoming true
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made true by the action Act.
%

eps_p((_=_),_,_) :- !, fail.
eps_p(P,A,E) :-
    bagof(Et,eps_p1(P,A,Et),Ets),
    joinlist((|),Ets,Ej),
    % use copy_fml to ensure no sharing of variables
    copy_fml(Ej,E).

%
%  eps_n(+F,?Act,?Cond) - conditions for a fluent becoming false
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made false by the action Act.
%
eps_n((_=_),_,_) :- !, fail.
eps_n(P,A,E) :-
    bagof(Et,eps_n1(P,A,Et),Ets),
    joinlist((|),Ets,Ej),
    % use copy_fml to ensure no sharing of variables
    copy_fml(Ej,E).

%
%  eps_p1(+F,?Act,?Cond) - individual conditions for truthifying a fluent
%
%  This preciate enumerates the different ways in which the fluent F can become
%  true, which are collected by eps_p/4.
%

eps_p1((P & Q),A,E) :-
    % Avoid generating redundant conjuncts be treating all the and
    % terms individually.
    flatten_op('&',[P,Q],Cls),
    maplist(eps_p1_andcls(A),Cls,Els),
    joinlist('&',Els,E).

eps_p1_andcls(A,P,E) :-
    eps_p(P,A,Ep),
    ( eps_n(P,A,En) ->
        E = (Ep | (P & -En))
    ;
        E = (Ep | P)
    ), !.
eps_p1_andcls(A,P,E) :-
    eps_n(P,A,En),
    E = (P & -En), !.
eps_p1_andcls(_,P,P).


eps_p1((P | _),A,E) :-
    eps_p(P,A,E).
eps_p1((_ | Q),A,E) :-
    eps_p(Q,A,E).

eps_p1(-P,A,E) :-
    eps_n(P,A,E).

eps_p1(all(X,P),A,E) :-
    eps_p(P,A,EP),
    % Since all(X,P) is to *become* true, we assume that it is currently
    % false, so exists(X,-P).  This legitimises moving any components of
    % EP that are independent of X outside the quantification, since the
    % EP part must be satisfied by at least one combination of variables.
    % This tends to greatly help simplification of the resuling formula.
    %
    % TODO: a rigorous proof of that this is OK...
    flatten_op('&',[EP],EPTerms),
    split_matching(EPTerms,indep_of_vars(X),Indep,Dep),
    ( Indep = [] ->
        IndepP = true
    ;
        joinlist('&',Indep,IndepP)
    ),
    ( Dep = [] ->
        DepP = true
    ;
        joinlist('&',Dep,DepP)
    ),
    % With that behind us, we can construct the output term
    ( eps_n(P,A,EPn) ->
        E = all(X,((P & -EPn) | DepP)) & IndepP
    ;
        E = all(X,P | DepP) & IndepP
    ).

eps_p1(exists(X,P),A,E) :-
    eps_p(P,A,EP),
    E = exists(X,EP).

eps_p1(P,A,E) :-
    causes_true(P,A,E).

% eps_p1(B=C,A,false).   is implicit


%
%  eps_n1(+F,?Act,?Cond) - individual conditions for falsifying a fluent
%
%  This preciate enumerates the different ways in which the fluent F can become
%  false, which are collected by eps_n/4.
%
%  We 'cheat' by defining them in terms of eps_p, based on DeMorgan's laws.
%

eps_n1((P & Q),A,E) :-
    eps_p1((-P) | (-Q),A,E).

eps_n1((P | Q),A,E) :-
    eps_p1((-P) & (-Q),A,E).

eps_n1(-P,A,E) :-
    eps_p1(P,A,E).

eps_n1(all(X,P),A,E) :-
    eps_p1(exists(X,-P),A,E).

eps_n1(exists(X,P),A,E) :-
    eps_p1(all(X,-P),A,E).

eps_n1(P,A,E) :-
    causes_false(P,A,E).

% eps_n1(B=C,A,false).   is implicit


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

%  If A is free, find all actions which could affect it.
%  TODO: eps_p currently cuts over action variables, so this doesnt work
regression(F,A,Fr) :-
    var(A), throw(regression_action_unbound),
    (bagof(Ft,B^regression_bagof(F,A,B,Ft),Fts) ->
        joinlist((|),Fts,Ftmp),
        simplify_c(Ftmp,Fr)
    ;
        Fr=F
    ).

regression_bagof(F,A,B,Ft) :-
    regression1(F,B,Ftp),
    (
      var(B), Ft=Ftp
    ;
      nonvar(B), Ft=(Ftp & (A=B))
    ).


%%  Regression is special-cased for the logical operators, as this
%%  produces smaller formulae than using eps_p/eps_n directly.
%%
regression1(F,A,Fr) :-
    is_literal(F),
    eps_p(F,A,Ep),
    eps_n(F,A,En),
    simplify_c(Ep | (F & -En),Fr).
regression1(F,A,Fr) :-
    is_literal(F),
    eps_p(F,A,Ep), 
    \+ eps_n(F,A,_),
    simplify_c(Ep | F,Fr).
regression1(F,A,Fr) :-
    is_literal(F),
    eps_n(F,A,En), 
    \+ eps_p(F,A,_),
    simplify_c(F & -En,Fr).
regression1(F,A,Fr) :-
    is_literal(F),
    \+ eps_n(F,A,_), 
    \+ eps_p(F,A,_),
    F = Fr.

regression1(all(X,P),A,all(X,R)) :-
    regression1(P,A,R).
regression1(exists(X,P),A,exists(X,R)) :-
    regression1(P,A,R).
regression1(-P,A,-R) :-
    regression1(P,A,R).
regression1((C=B),_,(C=B)).
regression1((P & Q),A,(R & S)) :-
    regression1(P,A,R),
    regression1(Q,A,S).
regression1((P | Q),A,(R | S)) :-
    regression1(P,A,R),
    regression1(Q,A,S).


%
%  holds(+F,+S) - fluent F holds in situation S
%
%  This predicate is true whenever the fluent F holds in situation S.
%
holds(true,_).
holds(A=B,_) :-     % no functional fluents, so equality does not vary
    A=B.
holds(-(A=B),_) :- 
    dif(A,B).
holds(F,do(A,S)) :-
    regression(F,A,Fr),
    holds(Fr,S).
holds(F1 -> F2,s0) :-
    holds(-F1,s0) ; holds(F2,s0).
holds(F1 <-> F2,s0) :-
    holds(F1,s0) , holds(F2,s0)
    ;
    holds(-F1,s0) , holds(-F2,s0).
holds(F1 & F2,s0) :-
    holds(F1,s0), holds(F2,s0).
holds(F1 | F2,s0) :-
    holds(F1,s0) ; holds(F2,s0).
holds(all(V,F),s0) :-
    holds(-exists(V,-F),s0).
holds(exists([],F),s0) :-
    holds(F,s0).
% TODO: should we assert that V is in the proper domain?
holds(exists([V:_|T],F),s0) :-
    subs(V,_,F,F1), holds(exists(T,F1),s0).
holds(-(F1 -> F2),s0) :- 
    holds((F1 & (-F2)),s0).
holds(-(F1 <-> F2),s0) :- 
    holds((F1 & (-F2) | ((-F1) & F2)),s0).
holds(-(F1 & F2),s0) :- 
    holds((-F1) | (-F2),s0).
holds(-(F1 | F2),s0) :-
    holds((-F1) & (-F2),s0).
holds(-all(V,F),s0) :-
    holds(exists(V,F),s0).
holds(-exists(V,F),s0) :-
    \+ holds(exists(V,F),s0).
holds(F,s0) :-
    prim_fluent(Ft),
    functor(Ft,S,N), functor(F,S,N),
    initially(F).
holds(-F,s0) :-
    prim_fluent(Ft),
    functor(Ft,S,N), functor(F,S,N),
    \+ initially(F).

%
%  "definition" version of knows/3
%  Calculates the entire persistence condition before regressing.
%  Here for informative purposes only.  The real version regresses
%  each component of the pcond before calculating the next, to save
%  calls into entails() for something that cant possibly lead
%  to a yes answer.
%

adp_fluent(legUnobs(Agt),A,C) :-
    adp_fluent(poss,A,C1),
    adp_fluent(canObs(Agt),A,C2),
    C = C1 & -C2.

knows(Agt,F,[]) :-
    pcond(F,legUnobs(Agt),P),
    holds(P,s0), !.
knows(Agt,F,[A|T]) :-
    pcond(F,legUnobs(Agt),P),
    regression(P,A,R),
    adp_fluent(poss,A,Poss),
    knows(Agt,(-Poss | R),T), !.

%
%  Implementation version of knows/3
%

knows(Agt,F,H) :-
    domain_axioms(Axs),
    knows(Agt,Axs,F,H).

knows(Agt,Axs,F,[]) :-
    ( entails(Axs,F) ->
        true
    ;
        holds(F,s0),
        pcond_d1(F,legUnobs(Agt),P1),
        add_to_axioms(F,Axs,Axs2),
        knows(Agt,Axs2,P1,[])
    ).
knows(Agt,Axs,F,[A|T]) :-
    ( entails(Axs,F) ->
        true
    ;
        regression(F,A,R),
        adp_fluent(poss,A,Poss),
        knows(Agt,(-Poss | R),T),
        pcond_d1(F,legUnobs(Agt),P1),
        add_to_axioms(F,Axs,Axs2),
        knows(Agt,Axs2,P1,[A|T])
    ).

