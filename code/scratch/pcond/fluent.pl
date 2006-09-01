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
%  directly.  We assume the name of the skolem fluent is "skol".
%


%
%  Our logical operators are the standard TSTP format operators:
% 
%     P & Q       -   logical and
%     P | Q       -   logical or
%     P => Q      -   implication
%     P <=> Q     -   equivalence
%     ~P          -   negation
%     !([X]:P)    -   universal quantification
%     ?([X]:P)    -   existential quantification
%     A = B       -   object equality
%     
%  Most of these are native prolog operators so we dont have
%  to declare them ourselves.  Note that ! and ?
%  take a list variables as their first argument - this
%  allows more compact quantification over multiple variables.
%

:- op(500, yfx, <=>).
:- op(500, yfx, =>).
:- op(500, yfx, &).
:- op(500, yfx, :).
:- op(550, fx, !).
:- op(550, fx, ?).
:- op(200,fy,~).


%
%  normalize(F,N) - perform some basic normalisations on a formula
%
%  This is designed to make formulae easier to reason about.  It
%  basically re-arranges orderless terms into a standard order, for
%  example the arguments to '=' and the list of variables in a
%  quantification.
% 
normalize((A=B),(A=B)) :-
    A @< B, !.
normalize((A=B),(B=A)) :-
    B @< A, !.
normalize((A=B),true) :-
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
normalize(P,P). 


%
%  struct_equiv(P,Q)  -  two formulae are structurally equivalent,
%                        basically meaning they are identical up
%                        to renaming of variables.
%
%  struct_oppos(P,Q)  -  two formulae are structurally opposite,
%                        making their conjunction a trivial falsehood.

struct_equiv(P,Q) :-
    struct_equiv(P,Q,[],_).

pairvars(A,B,A^B).

:- index(struct_equiv(1,1,0,0)).

struct_equiv(P,Q,VPairs,VPairs) :-
    var(P), !, var(Q), (P==Q ; ismember(P^Q,VPairs)), !.
struct_equiv(P,Q,VPairs,VPairs) :-
    var(Q), !, var(P), (P==Q ; ismember(P^Q,VPairs)), !.
struct_equiv(P,Q,VPairs,VPairs2) :-
    is_atom(P), is_atom(Q),
    nonvar(P), nonvar(Q),
    P =.. [F|ArgsP],
    Q =.. [F|ArgsQ],
    struct_equiv_list(ArgsP,ArgsQ,VPairs,VPairs2).
struct_equiv(P & Q,R & S,VPairs,VPairs2) :-
    struct_equiv(P,R,VPairs,VPairs1),
    struct_equiv(Q,S,VPairs1,VPairs2).
struct_equiv(P | Q,R | S,VPairs,VPairs2) :-
    struct_equiv(P,R,VPairs,VPairs1),
    struct_equiv(Q,S,VPairs1,VPairs2).
struct_equiv(P => Q,R => S,VPairs,VPairs2) :-
    struct_equiv(P,R,VPairs,VPairs1),
    struct_equiv(Q,S,VPairs1,VPairs2).
struct_equiv(P <=> Q,R <=> S,VPairs,VPairs2) :-
    struct_equiv(P,R,VPairs,VPairs1),
    struct_equiv(Q,S,VPairs1,VPairs2).
struct_equiv(~P,~Q,VPairs,VPairs2) :-
    struct_equiv(P,Q,VPairs,VPairs2).
struct_equiv(!(VarsP:P),!(VarsQ:Q),VPairs,VPairs2) :-
    maplist(pairvars,VarsP,VarsQ,VPairsT),
    append(VPairsT,VPairs,VPairs1),
    struct_equiv(P,Q,VPairs1,VPairs2).
struct_equiv(?(VarsP:P),?(VarsQ:Q),VPairs,VPairs2) :-
    maplist(pairvars,VarsP,VarsQ,VPairsT),
    append(VPairsT,VPairs,VPairs1),
    struct_equiv(P,Q,VPairs1,VPairs2).

struct_equiv_list([],[],VP,VP).
struct_equiv_list([H1|T1],[H2|T2],VP,VP2) :-
    struct_equiv(H1,H2,VP,VP1),
    struct_equiv_list(T1,T2,VP1,VP2).


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
%                           meaning F1 -> -F2 and F2 -> -F1
%

contradictory(F1,F2) :-
    struct_oppos(F1,F2) -> true
    ;
    free_vars(F1,Vars1), member(V,Vars1),
    var_given_value(V,F1,B), var_given_value(V,F2,C),
    ground(B), ground(C), B \= C -> true
    ;
    fail.

%
%  fml_compare  -  provide a standard order over formula terms
%
%  This allows them to be sorted, have duplicates removed, etc.
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

%  Since we know that B is a variable, we do this test by making a copy,
%  grounding the copied variable, then checking for structural equivalence
%  with the original term.
%
contains_var(A,V) :-
    \+ ncontains_var(A,V).

ncontains_var(A,V) :-
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
    \+ functor(T,Q,2), !.
flatten_quant(Q,T,Acc,Vars,Body) :-
    T =.. [Q,V,T2],
    append(V,Acc,Acc2),
    flatten_quant(Q,T2,Acc2,Vars,Body).

%
%  flatten_quant_and_simp(Q,BodyIn,VarsIn,VarsOut,BodyOut)
%
%                  - flatten nested quantifiers, and apply simplification
%
%  Just like flatten_quant/5 above, but applies simplify/2 to the body
%  when it does not match the quantifier, in case its simplification
%  does match.
%
flatten_quant_and_simp(Q,T,VarsIn,VarsOut,Body) :-
    ( T =.. [Q,V,T2] ->
      append(V,VarsIn,Vars2),
      flatten_quant_and_simp(Q,T2,Vars2,VarsOut,Body)
    ;
      simplify_c(T,Tsimp),
      ( Tsimp =.. [Q,V,T2] ->
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
%  vdelete(List,Elem,Result) - like delete/3 but for variable lists
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
%  ncontains_varterm(P,V)  -  P does not contain the variable term V
%
ncontains_varterm(P,X) :-
    ncontains_var(P,X).

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
%  
%  simplify_c(F1,F2)  -  simplify a formula, with verification
%
%  This predicate acts as simplify/2, but checks that F1 and F2 are in
%  fact equivalent.  If not, it raises an exception.
%  
simplify(P,P) :-
    is_atom(P), P \= (_ = _).
simplify(P & Q,S) :-
    flatten_op('&',[P,Q],TermsT),
    maplist(simplify_c,TermsT,TermsS),
    sublist(\=(true),TermsS,TermsF),
    predsort(fml_compare,TermsF,Terms),
    (
        member(false,Terms) -> S=false
    ;
        length(Terms,0) -> S=true
    ;
        pairfrom(Terms,F1,F2), contradictory(F1,F2) -> S=false
    %;
    %   IDEA: valuate to eliminate variables 
    ;
        joinlist('&',Terms,S)
    ).
simplify(P | Q,S) :-
    flatten_op('|',[P,Q],TermsT),
    maplist(simplify_c,TermsT,TermsS),
    sublist(\=(false),TermsS,TermsF),
    predsort(fml_compare,TermsF,Terms),
    (
        member(true,Terms) -> S=true
    ;
        length(Terms,0) -> S=false
    ;
        pairfrom(Terms,F1,F2), struct_oppos(F1,F2) -> S=true
    ;
        joinlist('|',Terms,S)
    ).
simplify(P => Q,S) :-
    simplify_c(P,Sp),
    simplify_c(Q,Sq),
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
    simplify_c(P,Sp),
    simplify_c(Q,Sq),
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
    simplify_c(P,SP),
    (
        SP=false -> S=true
    ;
        SP=true -> S=false
    ;
        SP = ~P2 -> S=P2
    ;
        S = ~SP
    ).
simplify(!(Xs:P),S) :-
    ( Xs = [] -> simplify_c(P,S)
    ;
    flatten_quant_and_simp('!',P,Xs,VarsT,Body),
    sort(VarsT,Vars),
    (
        Body=false -> S=false
    ;
        Body=true -> S=true
    ;
        % Remove any useless variables
        split_matching(Vars,ncontains_varterm(Body),_,Vars2),
        ( Vars2 = [] ->
            S2 = Body
        ;
          % Push independent components outside the quantifier,
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
   ( Xs = [] -> simplify_c(P,S)
   ;
   flatten_quant_and_simp('?',P,Xs,VarsT,Body),
   sort(VarsT,Vars),
   (
       Body=false -> S=false
   ;
       Body=true -> S=true
   ;
       % Remove vars that are assigned a specific value, therefore useless
       member(T1,Vars), var_valuated(T1,Body,Body2) ->
           vdelete(Vars,T1,Vars2), simplify_c(?(Vars2:Body2),S)
   ;
       % Remove any useless variables
       split_matching(Vars,ncontains_varterm(Body),_,Vars2),
       ( Vars2 = [] ->
           S = Body
       ;
         % Push independent components outside the quantifier,
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
       ground(A), ground(B), A \= B -> S=false
   ;
       normalize((A=B),S)
   ).


simplify_c(F1,F2) :-
    !, simplify(F1,F2).

simplify_c(F1,F2) :-
    % Make sure there's no var sharing initially
    copy_term(F1,F1c),
    ( vars_are_unique(F1) ->
        true
    ;
        write(F1), nl,
        write('input fml has nonunique vars'),nl,nl,
        throw(simp_inonuniq)
    ),
    % Check that the two formulae remain equivalent, if we can do so safely
    ( F1 \= ?([]:_), F1 \= !([]:_) ->
        simplify(F1,F2),
        ( equiv(F1,F2) ->
            true
       ;
            write(F1), nl,
            write('simplifies to:'), nl,
            write(F2), nl,
            write('which is *NOT* equivalent'), nl, nl, throw(simp_unequiv)
        )
    ;
        simplify(F1,F2)
    ),
    % Ensure that we havent produced any variable sharing.
    ( vars_are_unique(F2) ->
        true
    ;
        write('introduced non-unique vars'), nl,
        write(F1c), nl,
        write(F2), nl,
        nl, nl, throw(simp_nonuniq)
    ).


%
%  var_given_value(X,P,V)  -  variable X is uniformly given the value V
%                             within the formula P.

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
   % TODO: this is another possible simplification - a var given two values
   member(C,Cs), var_given_value(X,C,V).
var_given_value(X,P | Q,V) :-
   flatten_op('|',[P,Q],Cs),
   var_given_value_list(X,Cs,V).
var_given_value(X,!(_:P),V) :-
    var_given_value(X,P,V).
var_given_value(X,?(_:P),V) :-
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
   rename_vars([X],P,[V],Q), !.

% There's some trickery here, we allow ourselves to distribute
% the and over an or if the or has a valuation.
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
fml2nnf(P,P).


%
%  is_atom(P)  -  the formula P is an atom, not a compound expression
%
is_atom(P) :-
    P \= (~_),
    P \= (_ => _),
    P \= (_ <=> _),
    P \= (_ & _),
    P \= (_ | _),
    P \= ?(_:_),
    P \= !(_:_).


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

%
%  rename_vars(Vars,F,NewVars,NewF)  -  rename the given variables to new
%                                       ones, producing a modified formula.
rename_vars(Vs,P,Vs2,P2) :-
    % 'clever' and hopefully faster way, using term introspection
    % rather than repeated calls to subs/4
    term_variables(P,PVars),
    split_matching(PVars,var_in_list(Vs),_,OtherVs),
    copy_term(P^Vs^OtherVs,P2^Vs2^OtherVs).


%
%  free_vars(Fml,Vars)  -  list of all free variables in the formula
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
terms_in_fml(CP,Terms) :-
    CP =.. [Q,_,P],
    memberchk(Q,[all,exists]),
    terms_in_fml(P,Terms).



%
%  vars_are_unique(F)  -  check that each quantified var in F is unique
%

vars_are_unique(Fml) :-
    vars_are_unique(Fml,[],_).

vars_are_unique(P,SoFar,SoFar) :-
    is_atom(P).
vars_are_unique(~P,SoFar,SoFar2) :-
    vars_are_unique(P,SoFar,SoFar2).
vars_are_unique(P & Q,SoFar,SoFar2) :-
    vars_are_unique(P,SoFar,SoFar1),
    vars_are_unique(Q,SoFar1,SoFar2).
vars_are_unique(P | Q,SoFar,SoFar2) :-
    vars_are_unique(P,SoFar,SoFar1),
    vars_are_unique(Q,SoFar1,SoFar2).
vars_are_unique(P => Q,SoFar,SoFar2) :-
    vars_are_unique(P,SoFar,SoFar1),
    vars_are_unique(Q,SoFar1,SoFar2).
vars_are_unique(P <=> Q,SoFar,SoFar2) :-
    vars_are_unique(P,SoFar,SoFar1),
    vars_are_unique(Q,SoFar1,SoFar2).
vars_are_unique(!(V:P),SoFar,SoFar2) :-
    \+ ( member(X,V), ismember(X,SoFar) ),
    append(V,SoFar,SoFar1),
    vars_are_unique(P,SoFar1,SoFar2).
vars_are_unique(?(V:P),SoFar,SoFar2) :-
    \+ ( member(X,V), ismember(X,SoFar), write('DUPL VAR: '), write(X), nl ),
    append(V,SoFar,SoFar1),
    vars_are_unique(P,SoFar1,SoFar2).

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

