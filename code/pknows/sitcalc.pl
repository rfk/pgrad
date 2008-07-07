
:- multifile(adp_fluent/3).
:- index(adp_fluent(1,1,0)).
:- multifile(constraint/1).
:- multifile(initially/1).
:- multifile(holds0/1).
:- multifile(knows0/1).

:- discontiguous(causes_true/3).
:- discontiguous(causes_false/3).

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
awv_collect([T|Ts],[Y|Ys],[Y^T|Vs]) :-
    awv_collect(Ts,Ys,Vs).


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
initially(~knows(Agt,false)) :-
    agent(Agt).

domain_falsehood(Fml) :-
    domain_axioms(Axs),
    entails(Axs,~Fml).
domain_tautology(Fml) :-
    domain_axioms(Axs),
    entails(Axs,Fml).

%
%  Make adp_fluent enumerate action types if A is a variable
%
adp_fluent(F,A,C) :-
    var(A), !,
    (bagof(Ft,adp_fluent_bagof(F,A,Ft),Fts) ->
        joinlist((|),Fts,Ftmp),
        simplify(Ftmp,C)
    ;
        C=F
    ).

adp_fluent_bagof(F,A,F1) :-
    action_with_vars(A1,V),
    adp_fluent(F,A1,F1t),
    F1 = ?(V : (F1t & (A=A1))).

%
%  Useful ADPs that can be defined in terms of other, simpler ADPs
%

adp_fluent(pbu(Agt),A,C) :-
    adp_fluent(poss,A,C1),
    adp_fluent(canObs(Agt),A,C2),
    C = C1 & ~C2.

adp_fluent(obs(Agt,O),A,C) :-
    adp_fluent(canObs(Agt),A,CO),
    adp_fluent(canSense(Agt),A,CS),
    adp_fluent(sr(R),A,CR),
    C = ((~CO & (O=nil)) | (CO & ~CS & (O=A)) | (CO & CS & ?([R^result]: CR & (O=pair(A,R))))).


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
    simplify(Frt,Fr).

%  If A is free, find all actions which could affect F.
regression(F,A,Fr) :-
    var(A),
    (bagof(Ft,B^regression_bagof(F,A,B,Ft),Fts) ->
        joinlist((|),Fts,Ftmp),
        simplify(Ftmp,Fr)
    ;
        Fr=F
    ).

regression_bagof(F,A,B,Ft) :-
    action_with_vars(B,V),
    regression1(F,B,Ftr),
    Ft = ?(V : (Ftr & (A=B))).


% Regression base case, a primitive fluent.
% Build successor state axiom from causes_true/cases_false
regression1(F,A,Fr) :-
    is_atom(F), F \= (_ = _), F \= (_ \= _),
    (causes_true(F,A,Ep) -> true ; Ep = false),
    (causes_false(F,A,En) -> true ; En = false),
    simplify(Ep | (F & ~En),Fr).

% Regression of a knowledge expression.
%
% Since we're defining obs() in terms of canObs() and canSense(), we
% can make the following simplifications:
%
%    * replace obs()=nil with CanObs
%    * avoid quantifying over actions inside knows(), since only A
%      can ever match the observations for A
%
regression1(knows(Agt,P),A,Fr) :-
    Fr = ?([O^observation]: (ObsDefn & (~CanObs => knows(Agt,P)) & (CanObs => KR))),
    KR = knows(Agt,((Poss & ObsDefn2) => Ppr)),
    pcond(P,pbu(Agt),Pp),
    regression(Pp,A,Ppr),
    adp_fluent(obs(Agt,O),A,ObsDefn),
    adp_fluent(obs(Agt,O),A,ObsDefn2),
    adp_fluent(canObs(Agt),A,CanObs),
    adp_fluent(poss,A,Poss).
    

% No functional fluents, so equality is rigid
regression1(T1=T2,_,T1=T2).
regression1(T1\=T2,_,T1\=T2).

% Regression is pushed inside the logical operators
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
regression1((P => Q),A,(R => S)) :-
    regression1(P,A,R),
    regression1(Q,A,S).
regression1((P <=> Q),A,(R <=> S)) :-
    regression1(P,A,R),
    regression1(Q,A,S).


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
holds(F,s0) :-
    regression_s0(F,Fr),
    bagof(Ax,initially(Ax),Ax0s),
    joinlist('&',Ax0s,Ax0),
    domain_tautology(Ax0 => Fr).

regression_s0(F,F) :-
    is_atom(F).
regression_s0(knows(Agt,P),knows(Agt,Pp)) :-
    pcond(P,pbu(Agt),Pp).
regression_s0(!(X : P),!(X : R)) :-
    regression_s0(P,R).
regression_s0(?(X : P),?(X : R)) :-
    regression_s0(P,R).
regression_s0(~P,~R) :-
    regression_s0(P,R).
regression_s0((P & Q),(R & S)) :-
    regression_s0(P,R),
    regression_s0(Q,S).
regression_s0((P | Q),(R | S)) :-
    regression_s0(P,R),
    regression_s0(Q,S).
regression_s0((P => Q),(R => S)) :-
    regression_s0(P,R),
    regression_s0(Q,S).
regression_s0((P <=> Q),(R <=> S)) :-
    regression_s0(P,R),
    regression_s0(Q,S).


%
%  pcond_d1(F,C,P1)  -  depth 1 persistence condition for fluent F
%
%    The basic meaning of this pedicate is: if fluent F holds in situation
%    s, then it will continue to hold in all C-successors of s as long
%    as P1 is true in s.
% 

pcond_d1(F,C,P1) :-
    ( bagof(Cn,pcond_d1_bagof(F,C,Cn),Cns) ->
        joinlist('&',Cns,P1t),
        simplify(P1t,P1)
    ;
        P1=true
    ).

pcond_d1_bagof(F,C,Cnt) :-
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
    pcond_d1(F,C,P1),
    %length([F|Fs],Len), write('P'), write(Len), write('=  '), write(P1), nl,
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



enumerate_vars([]).
enumerate_vars([V^T|Vs]) :-
    call(T,V), enumerate_vars(Vs).


guess_var_types([],_,[]).
guess_var_types([V|Vs],P,[V^T|Ts]) :-
    guess_var_type(V,P,T),
    guess_var_types(Vs,P,Ts).

guess_var_type(V,P,T) :-
    (guess_var_type_(V,P,T2) -> T=T2 ; T=object), !.

guess_var_type_(V,P,T) :-
    is_atom(P), P \= (_=_), P \= (_\=_),
    contains_var(P,V^T),
    P =.. [F|FArgs], length(FArgs,NumArgs),
    length(FTypes,NumArgs), P2 =.. [F|FTypes],
    prim_fluent(P2),
    guess_var_type_list(V,FArgs,FTypes,T).
guess_var_type_(V,P1 & P2,T) :-
    guess_var_type_(V,P1,T) ; guess_var_type_(V,P2,T).
guess_var_type_(V,P1 | P2,T) :-
    guess_var_type_(V,P1,T) ; guess_var_type_(V,P2,T).
guess_var_type_(V,P1 => P2,T) :-
    guess_var_type_(V,P1,T) ; guess_var_type_(V,P2,T).
guess_var_type_(V,P1 <=> P2,T) :-
    guess_var_type_(V,P1,T) ; guess_var_type_(V,P2,T).
guess_var_type_(V,~P,T) :-
    guess_var_type_(V,P,T).
guess_var_type_(V,?(_:P),T) :-
    guess_var_type_(V,P,T).
guess_var_type_(V,!(_:P),T) :-
    guess_var_type_(V,P,T).
guess_var_type_(V,knows(_,P),T) :-
    guess_var_type_(V,P,T).
guess_var_type_(V,pknows(_,P),T) :-
    guess_var_type_(V,P,T).

guess_var_type_list(_,[],[],_) :- fail.
guess_var_type_list(V,[Ah|At],[Th|Tt],T) :-
    ( V == Ah ->
        T = Th
    ;
        guess_var_type_list(V,At,Tt,T)
    ).

