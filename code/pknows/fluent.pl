%
%  fluent.pl:  predicates for manipulating fluent terms
%
%  This file supplies the basic predicates for manipulating and reasoning
%  about fluent terms.
%
%  Variables are expected to be actual prolog variables, as this vastly
%  increases the simplicity and efficiency of certain operations.  It also
%  means we need to take extra care in some other areas.  In particular,
%  we assume that the formula contains the *only* references to those
%  variables, so we are free to bind them in simplification and reasoning.
%
%  In addition to manipulating arbitrary formulae, we have the ability
%  to put fluents into Clause Normal Form and manipulate this form
%  directly.  We assume the name of the skolem fluent is "skolN" where
%  N is the number of arguments *apart* from the situation argument.
%
%


%
%  Our logical operators are almost the standard TSTP format operators,
%  along with knows() and pknows() modalities:
% 
%     P & Q       -   logical and
%     P | Q       -   logical or
%     P => Q      -   implication
%     P <=> Q     -   equivalence
%     ~P          -   negation
%     !([X^T]:P)  -   universal quantification
%     ?([X^T]:P)  -   existential quantification
%     A = B       -   object equality
%     A \= B      -   object inequality
%     knows(A,P)  -   individual-level knowledge modality
%     pknows(E,P) -   complex epistemic modality
%
%  If I can make prolog accept '!=' as an operator, I'll use that for
%  inequality as well.
%     
%  Most of these are native prolog operators so we dont have
%  to declare them ourselves.  Note that ! and ?
%  take a list variables as their first argument - this
%  allows more compact quantification over multiple variables.
%
%  Also note that variables are paired with their type in the quantifier.
%

:- op(200,fx,~).
:- op(500, xfy, <=>).
:- op(500, xfy, =>).
:- op(520, xfy, &).
:- op(1200, xfx, :).
:- op(550, fx, !).
:- op(550, fx, ?).


%
%  normalize(F,N) - perform some basic normalisations on a formula
%
%  This is designed to make formulae easier to reason about.  It
%  re-arranges orderless terms into a standard order, for example
%  the arguments to '=' and the list of variables in a quantification.
%  It also simplifies away some trivial tautologies.
% 
normalize((A=B),(A=B)) :-
    A @< B, !.
normalize((A=B),(B=A)) :-
    B @< A, !.
normalize((A=B),true) :-
    A == B, !.
normalize((A\=B),(A\=B)) :-
    A @< B, !.
normalize((A\=B),(B\=A)) :-
    B @< A, !.
normalize((A\=B),false) :-
    A == B, !.
normalize(?(X:P),?(Y:Q)) :-
    sort(X,Y),
    normalize(P,Q), !.
normalize(!(X:P),!(Y:Q)) :-
    sort(X,Y),
    normalize(P,Q), !.
normalize(~P,~Q) :-
    normalize(P,Q), !.
normalize((P1 & Q1),(P2 & Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize((P1 | Q1),(P2 | Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize((P1 => Q1),(P2 => Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize((P1 <=> Q1),(P2 <=> Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize(knows(A,P),knows(A,Q)) :-
    normalism(P,Q), !.
normalize(pknows(E,P),pknows(E,Q)) :-
    normalism(P,Q), !.
normalize(P,P). 


%
%  struct_equiv(P,Q)  -  two formulae are structurally equivalent,
%                        basically meaning they are identical up
%                        to renaming of variables.
%
%  struct_oppos(P,Q)  -  two formulae are structurally opposed,
%                        making their conjunction a trivial falsehood.
%

struct_equiv(P,Q) :-
    P =@= Q.

struct_oppos(P,Q) :-
    P = ~P1, struct_equiv(P1,Q) -> true
    ;
    Q = ~Q1, struct_equiv(P,Q1) -> true
    ;
    P=true, Q=false -> true
    ;
    P=false, Q=true.


%
%  contradictory(F1,F2)  -  F1 and F2 are trivially contradictory,
%                           meaning F1 -> ~F2 and F2 -> ~F1
%

contradictory(F1,F2) :-
    struct_oppos(F1,F2) -> true
    ;
    free_vars(F1,Vars1), member(V1,Vars1),
    free_vars(F2,Vars2), member(V2,Vars2),
    V1 == V2,
    var_given_value(V1,F1,B), var_given_value(V2,F2,C),
    (\+ unifiable(B,C,_)) -> true
    ;
    fail.

%
%  fml_compare  -  provide a standard order over formula terms
%
%  This allows them to be sorted, have duplicates removed, etc.
%  Formula should be normalised before this is applied.
%
fml_compare('=',F1,F2) :-
    struct_equiv(F1,F2), !.
fml_compare(Ord,F1,F2) :-
    ( F1 @< F2 ->
        Ord = '<'
    ;
        Ord = '>'
    ).


%
%  contains_var(A,V)  -  formula A contains variable V
%
%  ncontains_var(A,V)  -  formula A does not contain variable V
%
%
%  Since we know that V is a variable, we do this test by making a copy,
%  grounding the copied variable, then checking for structural equivalence
%  with the original term.
%
contains_var(A,V^_) :-
    copy_term(A^V,A2^V2),
    V2=groundme,
    A \=@= A2.

ncontains_var(A,V^_) :-
    copy_term(A^V,A2^V2),
    V2=groundme,
    A =@= A2.
    

%
%  flatten_op(Op,Terms,Result) - flatten repeated ops into a list
%
%  This precicate succeeds when Result is a list of terms from Terms,
%  which were joined by the operator Op.  Basically allows a tree of
%  similar operators such as ((A & B) & (C & (D & E))) to be flattened
%  into a list (A,B,C,D,E).
%
flatten_op(O,Ts,Res) :-
    flatten_op(O,Ts,[],Res).

%  accumulator implementation of flatten_op/3

:- index(flatten_op(0,1,0,0)).

flatten_op(_,[],Res,Res).
flatten_op(O,[T|Ts],Acc,Res) :-
    ( T =.. [O|Args] ->
        append(Args,Ts,Ts2),
        flatten_op(O,Ts2,Acc,Res)
    ;
        flatten_op(O,Ts,[T|Acc],Res)
    ).

%
%  flatten_quant(Q,Ts,VarsIn,VarsOut,Body) - flatten nested quantifiers
%
flatten_quant(Q,T,Vars,Vars,T) :-
    \+ functor(T,Q,1), !.
flatten_quant(Q,T,Acc,Vars,Body) :-
    T =.. [Q,(V : T2)],
    append(V,Acc,Acc2),
    flatten_quant(Q,T2,Acc2,Vars,Body).

%
%  flatten_quant_and_simp(Q,BodyIn,VarsIn,VarsOut,BodyOut)
%       - flatten nested quantifiers, and apply simplification
%
%  Just like flatten_quant/5 above, but applies simplify/2 to the body
%  when it does not match the quantifier, in case its simplification
%  does match.
%
flatten_quant_and_simp(Q,T,VarsIn,VarsOut,Body) :-
    ( T =.. [Q,(V : T2)] ->
      append(V,VarsIn,Vars2),
      flatten_quant_and_simp(Q,T2,Vars2,VarsOut,Body)
    ;
      simplify(T,Tsimp),
      ( Tsimp =.. [Q,(V : T2)] ->
          append(V,VarsIn,Vars2),
          flatten_quant_and_simp(Q,T2,Vars2,VarsOut,Body)
      ;
          Body = Tsimp, VarsIn = VarsOut
      )
    ).


%
%  ismember(Elem,List)  -  like member/2, but does not bind variables or
%                          allow backtracking.
%
ismember(_,[]) :- fail.
ismember(E,[H|T]) :-
    ( E == H ->
        true
    ;
        ismember(E,T)
    ).

%
%  vdelete(List,Elem,Result) - like delete/3 but using equivalence rather
%                              than unification, so it can be used on lists
%                              of variables
%
vdelete([],_,[]).
vdelete([H|T],E,Res) :-
    ( E == H ->
        vdelete(T,E,Res)
    ;
        Res = [H|T2],
        vdelete(T,E,T2)
    ).

%
%  split_matching(List,Pred,Y,N)  -  splits List into elements that match Pred
%                                    (Y) and elements that dont (N)
%
split_matching([],_,[],[]).
split_matching([E|T],Pred,Y,N) :-
    ( call(Pred,E) ->
        Y = [E|YT],
        split_matching(T,Pred,YT,N)
    ;
        N = [E|NT],
        split_matching(T,Pred,Y,NT)
    ).


%
%  indep_of_vars(Vars,P)  -  P contains none of the vars in the list Vars
%
indep_of_vars(Vars,P) :-
    \+ ( member(X,Vars), contains_var(P,X) ).


%
%  var_in_list(Var,VarL)  -  variable V is in the list VarL
%
var_in_list([],_) :- fail.
var_in_list([H|T],V) :-
    ( V == H ->
        true
    ;
        var_in_list(T,V)
    ).

%
%  pairfrom(L,E1,E2)  -  E1 and E2 are a pair of (different) elements from L
%
%  Like doing (member(E1,L), member(E2,L))  but more efficient, doesnt match
%  E1 and E2 to the same element, and doesnt generate permutations.
%
pairfrom([H1,H2|T],E1,E2) :-
    E1 = H1, ( E2 = H2 ; member(E2,T) )
    ;
    pairfrom([H2|T],E1,E2).

%
%  simplify(+F1,-F2) - simplify a formula
%  
%  This predicate applies some basic simplification rules to a formula
%  to eliminate redundancy and (hopefully) speed up future reasoning.
%  For maximum simplification, apply normalize/2 first.
%  
simplify(P,P) :-
    is_atom(P), P \= (_ = _), P \= (_ \= _).
simplify(P & Q,S) :-
    flatten_op('&',[P,Q],TermsT),
    simplify_conjunction(TermsT,TermsS),
    ( TermsS = [] ->
        S = true
    ;
        % This will remove duplicates, which includes struct_equiv formulae
        predsort(fml_compare,TermsS,Terms),
        joinlist('&',Terms,S)
    ).
simplify(P | Q,S) :-
    flatten_op('|',[P,Q],TermsT),
    simplify_disjunction(TermsT,TermsS),
    ( TermsS = [] ->
        S = false
    ;
        % This will remove duplicates, which includes struct_equiv formulae
        predsort(fml_compare,TermsS,Terms),
        joinlist('|',Terms,S)
    ).
simplify(P => Q,S) :-
    simplify(P,Sp),
    simplify(Q,Sq),
    (
        Sp=false -> S=true
    ;
        Sp=true -> S=Sq
    ;
        Sq=true -> S=true
    ;
        Sq=false -> S=(~Sp)
    ;
        S = (Sp => Sq)
    ).
simplify(P <=> Q,S) :-
    simplify(P,Sp),
    simplify(Q,Sq),
    (
        struct_equiv(P,Q) -> S=true
    ;
        struct_oppos(P,Q) -> S=false
    ;
        Sp=false -> S=(~Sq)
    ;
        Sq=true -> S=Sq
    ;
        Sq=false -> S=(~Sp)
    ;
        Sq=true -> S=Sp
    ;
        S = (Sp <=> Sq)
    ).
simplify(~P,S) :-
    simplify(P,SP),
    (
        SP=false -> S=true
    ;
        SP=true -> S=false
    ;
        SP = ~P2 -> S=P2
    ;
        SP = (A\=B) -> S=(A=B)
    ;
        S = ~SP
    ).
simplify(!(Xs:P),S) :-
    ( Xs = [] -> simplify(P,S)
    ;
    flatten_quant_and_simp('!',P,Xs,VarsT,Body),
    sort(VarsT,Vars),
    (
        Body=false -> S=false
    ;
        Body=true -> S=true
    ;
        % Remove any useless variables
        split_matching(Vars,ncontains_var(Body),_,Vars2),
        ( Vars2 = [] ->
            S2 = Body
        ;
          % Pull independent components outside the quantifier.
          % Both conjuncts and disjuncts can be handled in this manner.
          (flatten_op('|',[Body],BTerms), BTerms = [_,_|_] -> 
            split_matching(BTerms,indep_of_vars(Vars),Indep,BT2),
            % Because we have removed useless vars, BT2 cannot be empty
            joinlist('|',BT2,Body2),
            ( Indep = [] ->
              S2=!(Vars2:Body2)
            ;
              joinlist('|',Indep,IndepB),
              S2=(!(Vars2:Body2) | IndepB)
            )
          
          ; flatten_op('&',[Body],BTerms), BTerms = [_,_|_] ->
            split_matching(BTerms,indep_of_vars(Vars),Indep,BT2),
            joinlist('&',BT2,Body2),
            ( Indep = [] ->
              S2=!(Vars2:Body2)
            ;
              joinlist('&',Indep,IndepB),
              S2=(!(Vars2:Body2) & IndepB)
            )
          ;
            S2=!(Vars2:Body)
          )
        ),
        S = S2
    )).
simplify(?(Xs:P),S) :-
   ( Xs = [] -> simplify(P,S)
   ;
   flatten_quant_and_simp('?',P,Xs,VarsT,Body),
   sort(VarsT,Vars),
   (
       Body=false -> S=false
   ;
       Body=true -> S=true
   ;
       % Remove vars that are assigned a specific value, simply replacing
       % them with their value in the Body formula
       member(V1^T1,Vars), var_valuated(V1,Body,Body2) ->
           vdelete(Vars,V1^T1,Vars2), simplify(?(Vars2:Body2),S)
   ;
       % Remove any useless variables
       split_matching(Vars,ncontains_var(Body),_,Vars2),
       ( Vars2 = [] ->
           S = Body
       ;
         % Pull independent components outside the quantifier,
         % Both conjuncts and disjuncts can be handled in this manner.
         (flatten_op('|',[Body],BTerms), BTerms = [_,_|_] -> 
           split_matching(BTerms,indep_of_vars(Vars),Indep,BT2),
           joinlist('|',BT2,Body2),
           ( Indep = [] ->
             S = ?(Vars2:Body2)
           ;
             joinlist('|',Indep,IndepB),
             S = (?(Vars2:Body2) | IndepB)
           )
         ; flatten_op('&',[Body],BTerms), BTerms = [_,_|_] ->
           split_matching(BTerms,indep_of_vars(Vars),Indep,BT2),
           joinlist('&',BT2,Body2),
           ( Indep = [] ->
             S = ?(Vars2:Body2)
           ;
             joinlist('&',Indep,IndepB),
             S = (?(Vars2:Body2) & IndepB)
           )
         ;
           S = ?(Vars2:Body)
         )
       )
   )).
simplify((A=B),S) :-
   (
       A == B -> S=true
   ;
       % Utilising the unique names assumption
       (\+ unifiable(A,B,_)) -> S=false
   ;
       normalize((A=B),S)
   ).
simplify((A\=B),S) :-
   (
       A == B -> S=false
   ;
       % Utilising the unique names assumption
       (\+ unifiable(A,B,_)) -> S=true
   ;
       normalize((A\=B),S)
   ).
simplify(knows(A,P),S) :-
   simplify(P,Ps),
   ( Ps=true -> S=true
   ; Ps=false -> S=false
   ; S = knows(A,Ps)
   ).
simplify(pknows(E,P),S) :-
   simplify(P,Ps),
   ( Ps=true -> S=true
   ; Ps=false -> S=false
   ; S = pknows(E,Ps)
   ).


%
%  simplify_conjunction(In,Out)  -  simplify the conjunction of list of fmls
%  simplify_disjunction(In,Out)  -  simplify the disjunction of list of fmls
%

simplify_conjunction(FmlsIn,FmlsOut) :-
    maplist(simplify,FmlsIn,FmlsI2),
    simplify_conjunction_acc(FmlsI2,[],FmlsOut).

simplify_conjunction_acc([],FmlsAcc,FmlsAcc).
simplify_conjunction_acc([F|FmlsIn],FmlsAcc,FmlsOut) :-
    % TODO: can we simplify F relative to the accumulated conjuncts?
    %( joinlist('&',FmlsAcc,BG), fml_entails(BG,F) -> F2 = true ; F2 = F),
    F2 = F,
    ( F2=true ->
        simplify_conjunction_acc(FmlsIn,FmlsAcc,FmlsOut)
    ; F2=false ->
        FmlsOut=[false]
    ;
        simplify_conjunction_acc(FmlsIn,[F2|FmlsAcc],FmlsOut)
    ).
    

simplify_disjunction(FmlsIn,FmlsOut) :-
    maplist(simplify,FmlsIn,FmlsI2),
    simplify_disjunction_acc(FmlsI2,[],FmlsOut).

simplify_disjunction_acc([],FmlsAcc,FmlsAcc).
simplify_disjunction_acc([F|FmlsIn],FmlsAcc,FmlsOut) :-
    ( F=false ->
        simplify_disjunction_acc(FmlsIn,FmlsAcc,FmlsOut)
    ; F=true ->
        FmlsOut=[true]
    ;
        simplify_disjunction_acc(FmlsIn,[F|FmlsAcc],FmlsOut)
    ).


%
%  var_given_value(X,P,V)  -  variable X is uniformly given the value V
%                             within the formula P.
%
%  var_given_value_list(X,Ps,V)  -  variable X is uniformly given the value V
%                                   in all formulae in list Ps.

:- index(var_given_value(0,1,0)).
:- index(var_given_value_list(0,1,0)).

var_given_value(X,A=B,V) :-
    ( X == A ->
        V = B
    ;
        X == B, V = A
    ).
var_given_value(X,P & Q,V) :-
   flatten_op('&',[P,Q],Cs),
   member(C,Cs), var_given_value(X,C,V).
var_given_value(X,P | Q,V) :-
   flatten_op('|',[P,Q],Cs),
   var_given_value_list(X,Cs,V).
var_given_value(X,!(_:P),V) :-
    var_given_value(X,P,V).
var_given_value(X,?(_:P),V) :-
    var_given_value(X,P,V).
var_given_value(X,knows(_,P),V) :-
    var_given_value(X,P,V).
var_given_value(X,pknows(_,P),V) :-
    var_given_value(X,P,V).

var_given_value_list(_,[],_).
var_given_value_list(X,[H|T],V) :-
    var_given_value(X,H,V),
    var_given_value_list(X,T,V).

%
%  var_valuated(X,P,P2)  -  variable X takes specific values throughout P,
%                           and P2 is P with the appropriate valuations
%                           inserted.
%

:- index(var_valuated(0,1,0)).
:- index(var_valuated_list(0,1,0)).
:- index(var_valuated_distribute(0,1,0,0)).

var_valuated(X,P,Q) :-
   var_given_value(X,P,V),
   rename_vars([X^T],P,[V^T],Q), !.

% There's some trickery here, we allow ourselves to distribute
% the & over a | if the | has a valuation.
var_valuated(X,P & Q,V) :-
   flatten_op('&',[P,Q],Cls),
   select(Cl,Cls,Rest),
   flatten_op('|',[Cl],ClOrs),
   maplist(var_valuated_check(X),ClOrs),
   joinlist('&',Rest,RestTerm),
   var_valuated_distribute(X,ClOrs,RestTerm,Qs),
   joinlist('|',Qs,V), !.

var_valuated(X,P | Q,V) :-
   flatten_op('|',[P,Q],Cs),
   var_valuated_list(X,Cs,Vs),
   joinlist('|',Vs,V).
var_valuated(X,!(V:P),!(V:Q)) :-
    var_valuated(X,P,Q).
var_valuated(X,?(V:P),?(V:Q)) :-
    var_valuated(X,P,Q).

var_valuated_list(_,[],[]).
var_valuated_list(X,[H|T],[Hv|Tv]) :-
    var_valuated(X,H,Hv),
    var_valuated_list(X,T,Tv).

var_valuated_distribute(_,[],_,[]).
var_valuated_distribute(X,[P|Ps],Q,[Pv|T]) :-
    var_valuated(X,P & Q,Pv),
    var_valuated_distribute(X,Ps,Q,T).

var_valuated_check(X,F) :-
    var_given_value(X,F,_).


%
%  joinlist(+Op,+In,-Out) - join items in a list using given operator
%

joinlist(_,[H],H) :- !.
joinlist(O,[H|T],J) :-
    T \= [],
    J =.. [O,H,TJ],
    joinlist(O,T,TJ).

%
%  subs(Name,Value,Old,New):  substitue values in a term
%
%  This predicate is true when New is equal to Old with all occurances
%  of Name replaced by Value - basically, a symbolic substitution
%  routine.  For example, it is usually used to produce a result such
%  as:
%
%      subs(now,S,fluent(now),fluent(S)).
%
subs(X,Y,T,Tr) :-
    T == X, Tr = Y, !.
subs(X,_,T,Tr) :-
    T \== X, var(T), T=Tr, !.
subs(X,Y,T,Tr) :-
    T \== X, nonvar(T), T =.. [F|Ts], subs_list(X,Y,Ts,Trs), Tr =.. [F|Trs], !.

%
%  subs_list(Name,Value,Old,New):  value substitution in a list
%
%  This predicate operates as subs/4, but Old and New are lists of terms
%  instead of single terms.  Basically, it calls subs/4 recursively on
%  each element of the list.
%
subs_list(_,_,[],[]).
subs_list(X,Y,[T|Ts],[Tr|Trs]) :-
    subs(X,Y,T,Tr), subs_list(X,Y,Ts,Trs).


%
%  fml2nnf:  convert a formula to negation normal form
%
fml2nnf(P <=> Q,N) :-
    fml2nnf((P => Q) & (Q => P),N), !.
fml2nnf(P => Q,N) :-
    fml2nnf((~P) | Q,N), !.
fml2nnf(~(P & Q),N) :-
   fml2nnf((~P) | (~Q),N), !.
fml2nnf(~(P | Q),N) :-
   fml2nnf((~P) & (~Q),N), !.
fml2nnf(~(!(X:P)),N) :-
   fml2nnf( ?(X : ~P) ,N), !.
fml2nnf(~(?(X:P)),N) :-
   fml2nnf(!(X : ~P),N), !.
fml2nnf(~(~P),N) :-
    fml2nnf(P,N), !.
fml2nnf(P & Q,Np & Nq) :-
    fml2nnf(P,Np), fml2nnf(Q,Nq), !.
fml2nnf(P | Q,Np | Nq) :-
    fml2nnf(P,Np), fml2nnf(Q,Nq), !.
fml2nnf(!(X:P),!(X:N)) :-
    fml2nnf(P,N), !.
fml2nnf(?(X:P),?(X:N)) :-
    fml2nnf(P,N), !.
fml2nnf(knows(A,P),knows(A,N)) :-
    fml2nnf(P,N), !.
fml2nnf(pknows(E,P),pknows(E,N)) :-
    fml2nnf(P,N), !.
fml2nnf(P,P).


%
%  fml2cnf  -  convert formula to CNF
%
%  This will rename variables, so be careful!
%

fml2cnf(F,C) :-
    e_cnf(F,C).

cnf2fml([],true) :- !.
cnf2fml(C,F) :-
    maplist(djs2fml,C,Ds),
    joinlist('&',Ds,B),
    free_vars(B,V),
    ( V = [] ->
        F = B
    ;
        F = !(V : B)
    ).

djs2fml([],false) :- !.
djs2fml(D,F) :-
    joinlist('|',D,F).


%
%  is_atom(P)  -  the formula P is an atom, not a compound expression
%
is_atom(P) :-
    P \= [],
    P \= [_|_],
    P \= (~_),
    P \= (_ => _),
    P \= (_ <=> _),
    P \= (_ & _),
    P \= (_ | _),
    P \= ?(_:_),
    P \= !(_:_),
    P \= knows(_,_),
    P \= pknows(_,_).


%
%  copy_fml(P,Q)  -  make a copy of a formula.  The copy will have all
%                    bound variables renamed to new vars.  Any free variables
%                    will retain their original names.
%

copy_fml(P,P) :-
    var(P), !.
copy_fml(P,P) :-
    is_atom(P).
copy_fml(P & Q,R & S) :-
    copy_fml(P,R),
    copy_fml(Q,S).
copy_fml(P | Q,R | S) :-
    copy_fml(P,R),
    copy_fml(Q,S).
copy_fml(P => Q,R => S) :-
    copy_fml(P,R),
    copy_fml(Q,S).
copy_fml(P <=> Q,R <=> S) :-
    copy_fml(P,R),
    copy_fml(Q,S).
copy_fml(~P,~Q) :-
    copy_fml(P,Q).
copy_fml(!(VarsP:P),!(VarsQ:Q)) :-
    rename_vars(VarsP,P,VarsQ,P2),
    copy_fml(P2,Q).
copy_fml(?(VarsP:P),?(VarsQ:Q)) :-
    rename_vars(VarsP,P,VarsQ,P2),
    copy_fml(P2,Q).
copy_fml(knows(A,P),knows(A,Q)) :-
    copy_fml(P,Q).
copy_fml(pknows(E,P),pknows(E,Q)) :-
    copy_fml(P,Q).

%
%  rename_vars(Vars,F,NewVars,NewF)  -  rename the given variables to new
%                                       ones, producing a modified formula.
%
rename_vars(Vs,P,Vs2,P2) :-
    rename_vars(Vs,P,[],Vs2,P2).

rename_vars([],P,Acc,Acc,P).
rename_vars([V^T|Vs],P,Acc,NewV,NewP) :-
    subs(V,V2,P,P2),
    append(Acc,[V2^T],Acc2),
    rename_vars(Vs,P2,Acc2,NewV,NewP).

%
%  free_vars(Fml,Vars)  -  list of all free variables in the formula
%
%  "Free" is in the FOL sense of "not bound by an enclosing quantifier"
%
free_vars(Fml,Vars) :-
    copy_fml(Fml,Fml2),
    term_variables(Fml,Vars1),
    term_variables(Fml2,Vars2),
    vars_in_both(Vars1,Vars2,[],Vars).

vars_in_both([],_,Vars,Vars).
vars_in_both([H|T],V2,Acc,Vars) :-
    ( ismember(H,V2) ->
        vars_in_both(T,V2,[H|Acc],Vars)
    ;
        vars_in_both(T,V2,Acc,Vars)
    ).
    
%
%  terms_in_fml(F,Terms)  -  list all the basic terms found in the formula
%
terms_in_fml(P,Terms) :-
    is_atom(P), !,
    P =.. [_|Args],
    sublist(ground,Args,TermsT),
    sort(TermsT,Terms).
terms_in_fml(~P,Terms) :-
    !, terms_in_fml(P,Terms).
terms_in_fml(CP,Terms) :-
    CP =.. [Op,P1,P2],
    memberchk(Op,['&','|','=>','<=>']), !,
    terms_in_fml(P1,T1),
    terms_in_fml(P2,T2),
    oset_union(T1,T2,Terms).
terms_in_fml(!(_:P),Terms) :-
    terms_in_fml(P,Terms).
terms_in_fml(?(_:P),Terms) :-
    terms_in_fml(P,Terms).
terms_in_fml(knows(_,P),Terms) :-
    terms_in_fml(P,Terms).
terms_in_fml(pknows(_,P),Terms) :-
    terms_in_fml(P,Terms).


%
%  equiv(F1,F2)  -  check that two formulae are equivalent
%  equiv(Axs,F1,F2)  -  check that two formulae are equivalent, given axioms
%

equiv(F1,F2) :-
    fml2axioms(true & ~false,Axs),
    equiv(Axs,F1,F2).

equiv(Axs,F1,F2) :-
    entails(Axs,F1 => F2),
    entails(Axs,F2 => F1).

fml_entails(F1,F2) :-
    fml2axioms(F1,Axs),
    entails(Axs,F2).

write_eqn(P) :-
    write('\\begin{multline}'),nl,write_latex(P),nl,write('\\end{multline}').

write_latex(P) :-
  copy_fml(P,Pc),
  number_vars(Pc),
  do_write_latex(Pc).

do_write_latex(P) :-
    var(P), write(P), !.
do_write_latex(P <=> Q) :-
    do_write_latex(P), write(' \\equiv '), do_write_latex(Q).
do_write_latex(P => Q) :-
    do_write_latex(P), write(' \\rightarrow '), do_write_latex(Q).
do_write_latex(~P) :-
    write(' \\neg '), do_write_latex(P).
do_write_latex(P & Q) :-
    flatten_op('&',[P & Q],[C|Cs]),
    write(' \\left( '), do_write_latex(C), reverse(Cs,CsR),
    do_write_latex_lst(CsR,' \\wedge '), write(' \\right) ').
do_write_latex(P | Q) :-
    flatten_op('|',['|'(P,Q)],[C|Cs]),
    do_write_latex(C), reverse(Cs,CsR),
    do_write_latex_lst(CsR,' \\vee ').
do_write_latex(!([X|Xs]:P)) :-
    write(' \\forall '),
    do_write_latex(X),
    do_write_latex_lst(Xs,','),
    write(' : \\left[ '),
    do_write_latex(P),
    write(' \\right] ').
do_write_latex(?([X|Xs]:P)) :-
    write(' \\exists '),
    do_write_latex(X),
    do_write_latex_lst(Xs,','),
    write(' : \\left[ '),
    do_write_latex(P),
    write(' \\right] ').
do_write_latex(knows(A,P)) :-
    write(' \\Knows( '),
    do_write_latex(A),
    write(','),
    do_write_latex(P),
    write(')').
do_write_latex(pknows(E,P)) :-
    write(' \\PKnows( '),
    do_write_latex(E),
    write(','),
    do_write_latex(P),
    write(')').
do_write_latex(P) :-
    is_atom(P), write(P).

do_write_latex_lst([],_).
do_write_latex_lst([T|Ts],Sep) :-
    write(Sep), nl, do_write_latex(T), do_write_latex_lst(Ts,Sep).


number_vars(X) :-
    term_variables(X,Vs),
    number_vars_rec(Vs,0).
number_vars_rec([],_).
number_vars_rec([V|Vs],N) :-
    name(x,N1), name(N,N2), append(N1,N2,Codes),
    atom_codes(V,Codes),
    Ns is N + 1,
    number_vars_rec(Vs,Ns).

%
%  In conjunction with this file, one requires an implementation of actual
%  logical reasoning.  Such a reasoning engine, like this file, must enforce
%  unique names axioms for all ground terms in formulae - that is, for any
%  terms returned by terms_in_fml/2.
%
%  The following predicates are expected to be provided by an implementation
%  of logical reasoning.
%
%  fml2axioms(Fml,Axs):  Convert formula to more efficient form
%
%     This predicate is used to convert the formula in Fml into an opaque
%     form that can be used for efficient reasoning.
%
%  add_to_axioms(Fml,Axs,Axs2):  Add a formula to an existing set of axioms
%
%  combine_axioms(Ax1,Ax2,Axs):  Combine two sets of axioms
%
%  entails(Axioms,Conc):  Succeeds when conc is logically entailed by Axioms
%
%     This *must not* bind any variables in Conc.  The easiest way to
%     do so is to take a copy of Conc and work from that.
%



:- begin_tests(fluent).

test(simp1) :-
    simplify(p & true,p).
test(simp2) :-
    simplify(p & false,false).
test(simp3) :-
    simplify(p | false,p).
test(simp4) :-
    simplify(p | true,true).
test(simp5) :-
    simplify(false | false,false).
test(simp6) :-
    simplify(false | (p & ~(a=a)),false).
test(simp7) :-
    simplify(true & true,true).
test(simp8) :-
    simplify(!([X^t]: p(X) & p(a)),!([X^t]:p(X)) & p(a)).
test(simp9) :-
    simplify(?([X^t]: p(X) & p(a)),?([X^t]:p(X)) & p(a)).

test(copy1) :-
    F1 = !([X^t,Y^q] : p(X) & r(Y)),
    copy_fml(F1,F2),
    F1 =@= F2,
    F1 \== F2.

:- end_tests(fluent).


