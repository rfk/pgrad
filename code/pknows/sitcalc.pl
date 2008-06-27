
:- multifile(adp_fluent/3).
:- index(adp_fluent(1,1,0)).
:- multifile(constraint/1).
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
    is_atom(F), F \= (_ = _), F \= (_ \= _), F \= knows(_,_),
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


%
%  Test whether a given term is a fluent or action
%
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
holds(F,s0) :-
    holds0(F).

% holds0(F) is implemented in such a way as to allow open-world reasoning.
% We must push negation down onto the individual literals, so we can test
% them using primitive knows0 and holds0 from the domain.
% 
% First, using DeMorgan etc
%
holds0(F1 => F2) :-
    holds0(~F1) ; holds0(F2).
holds0(F1 <=> F2) :-
    holds0(F1) , holds0(F2)
    ;
    holds0(~F1) , holds0(~F2).
holds0(F1 & F2) :-
    holds0(F1), holds0(F2).
holds0(F1 | F2) :-
    holds0(F1) ; holds0(F2).
holds0(~(F1 => F2)) :- 
    holds0((F1 & (~F2))).
holds0(~(F1 <=> F2)) :- 
    holds0((F1 & (~F2) | ((~F1) & F2))).
holds0(~(F1 & F2)) :- 
    holds0((~F1) | (~F2)).
holds0(~(F1 | F2)) :-
    holds0((~F1) & (~F2)).
%
% Re-write quantifiers to be in positive form
%
holds0(~!(V : F)) :-
    holds0(?(V : ~F)).
holds0(~?(V : F)) :-
    holds0(!(V : ~F)).
%
%  Handle positive quantifiers by binding free variables.
%  For ? prolog does the hard work for us.
%  For ! we determine type of var and enumerate it into a conjunction.
%
holds0(?([] : F)) :-
    holds0(F).
holds0(?([V^_|Vs] : F)) :-
    subs(V,_,F,F1), holds0(?(Vs : F1)).
holds0(!([] : F)) :-
    holds0(F).
holds0(!([V^T|Vs] : F)) :-
    bagof(Fb,(Val^(call(T,Val),subs(V,Val,!(Vs:F),Fb))),Fbs),
    joinlist('&',Fbs,Enum),
    holds0(Enum).

%
%  For knowledge, apply persistence condition then just call into knows0.
%
holds0(knows(Agt,F)) :-
    pcond(F,pbu(Agt),P),
    knows0(P).
holds0(~knows(Agt,F)) :-
    pcond(F,pbu(Agt),P),
    \+ knows0(P).
%
%  Handle equality using unification
%
holds0(A=B) :-
    A=B.
holds0(~(A=B)) :- 
    dif(A,B).

%
%  Finally, we rely on holds0/1 from domain.pl to hande primitive fluents.
%  Assume that knows0 -> holds0
%
holds0(F) :-
    knows0(F).

%
%  knows0(Fml) is handled as per holds0(Fml)
%
knows0(F1 => F2) :-
    knows0(~F1) ; knows0(F2).
knows0(F1 <=> F2) :-
    knows0(F1) , knows0(F2)
    ;
    knows0(~F1) , knows0(~F2).
knows0(F1 & F2) :-
    knows0(F1), knows0(F2).
knows0(F1 | F2) :-
    knows0(F1) ; knows0(F2).
knows0(~(F1 => F2)) :- 
    knows0((F1 & (~F2))).
knows0(~(F1 <=> F2)) :- 
    knows0((F1 & (~F2) | ((~F1) & F2))).
knows0(~(F1 & F2)) :- 
    knows0((~F1) | (~F2)).
knows0(~(F1 | F2)) :-
    knows0((~F1) & (~F2)).
knows0(~!(V : F)) :-
    knows0(?(V : ~F)).
knows0(~?(V : F)) :-
    knows0(!(V : ~F)).
knows0(?([] : F)) :-
    knows0(F).
knows0(?([V^_|Vs] : F)) :-
    subs(V,_,F,F1), knows0(?(Vs : F1)).
knows0(!([] : F)) :-
    knows0(F).
knows0(!([V^T|Vs] : F)) :-
    bagof(Fb,(Val^(call(T,Val),subs(V,Val,!(Vs:F),Fb))),Fbs),
    joinlist('&',Fbs,Enum),
    knows0(Enum).
knows0(knows(Agt,F)) :-
    pcond(F,pbu(Agt),P),
    knows0(P).
knows0(~knows(Agt,F)) :-
    pcond(F,pbu(Agt),P),
    \+ knows0(P).

%
%  pcond_d1(F,C,P1)  -  depth 1 persistence condition for fluent F
%
%    The basic meaning of this pedicate is: if fluent F holds in situation
%    s, then it will continue to hold in all C-successors of s as long
%    as P1 is true in s.
% 

pcond_d1(F,C,P1) :-
    ( bagof(Cn,pcond_d1_bagof(F,C,Cn),Cns) ->
        simplify_conjunction(Cns,SimpCns),
        joinlist((&),SimpCns,P1)
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

