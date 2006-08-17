%
%  fml.pl:  predicates for handling logical formulae
%
%  This file supplies the basic predicates for manipulating logical
%  formulae.  These formulae will typically be used to represent
%  fluents, but I've tried to keep it as general as possible. The
%  only thing I'm assuming is the unique names axioms (just like
%  prolog).
%
%  Note that we're explicitly working in many-sorted first-order logic,
%  so each quantified variable must have an assocaited domain of
%  interpretation.  We also implicitly assume that we'll never construct
%  formulae that have sorts where they don't belong (this greatly
%  simplifies simplification).
%
%  Variables are expected to be actual prolog variables, as this vastly
%  increases the simplicity and efficiency of certain operations.  It also
%  means we need to take extra care in some other areas.  In particular,
%  we assume that the formula contains the *only* references to those
%  variables, so we are free to bind them in simplification and reasoning.
%


%
%  Our logical operators are:
% 
%     P & Q           -   logical and
%     P | Q           -   logical or
%     P -> Q          -   implication
%     P <-> Q         -   equivalence
%     -P              -   negation
%     all([X:D],P)    -   universal quantification
%     exists([X:D],P) -   existential quantification
%     A = B           -   object equality
%     
%  Most of these are native prolog operators so we dont have
%  to declare them ourselves.  Note that all() and exists()
%  take a list of typed variables as their first argument - this
%  allows more compact quantification over multiple variables.
%

:- op(500, yfx, <->).
:- op(500, yfx, &).


%
%  normalize(F,N) - perform some basic normalisations on a formula
%
%  This is designed to make formulae easier to reason about.  It
%  basically re-arranges orderless terms into a standard order, for
%  example the arguments to '=' of the list of variables in a
%  quantification.
% 
normalize((A=B),(A=B)) :-
    A @< B, !.
normalize((A=B),(B=A)) :-
    B @< A, !.
normalize((A=B),true) :-
    A == B, !.
normalize(exists(X,P),exists(Y,Q)) :-
    sort(X,Y),
    normalize(P,Q), !.
normalize(all(X,P),all(Y,Q)) :-
    sort(X,Y),
    normalize(P,Q), !.
normalize(-P,-Q) :-
    normalize(P,Q), !.
normalize((P1 & Q1),(P2 & Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize((P1 | Q1),(P2 | Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize((P1 -> Q1),(P2 -> Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize((P1 <-> Q1),(P2 <-> Q2)) :-
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
    P =@= Q.

struct_oppos(P,Q) :-
    P = -P1, struct_equiv(P1,Q) -> true
    ;
    Q = -Q1, struct_equiv(P,Q1) -> true
    ;
    P=true, Q=false -> true
    ;
    P=false, Q=true.


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
%  grounding the copied variable, then checking for structural equivalent
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
      simplify(T,Tsimp),
      ( Tsimp =.. [Q,V,T2] ->
          append(V,VarsIn,Vars2),
          flatten_quant_and_simp(Q,T2,Vars2,VarsOut,Body)
      ;
          Body = Tsimp, VarsIn = VarsOut
      )
    ).

%
%  vmember(Elem,List) - like member/2, but specific to our quant variable lists
%
%  Required because using member/2 would actually bind the variables in the
%  list, which we dont want.
%
vmember(_,[]) :- fail.
vmember(E:V,[H:U|T]) :-
    V=U, E == H
    ;
    vmember(E:V,T).

%
%  vdelete(List,Elem,Result) - like delete/3 but for quant variable lists
%
%  Obvious conterpart to vmember/2
%
vdelete([],_,[]).
vdelete([H:U|T],E:V,Res) :-
    ( V=U, E == H ->
        vdelete(T,E:V,Res)
    ;
        Res = [H:U|T2],
        vdelete(T,E:V,T2)
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
ncontains_varterm(P,X:_) :-
    ncontains_var(P,X).

%
%  indep_of_vars(Vars,P)  -  P contains none of the vars in the list Vars
%
indep_of_vars(Vars,P) :-
    \+ ( member(X:_,Vars), contains_var(P,X) ).
                                                      

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
    is_literal(P), P \= (_ = _).
simplify(P & Q,S) :-
    flatten_op('&',[P,Q],TermsT),
    maplist(simplify,TermsT,TermsS),
    sublist(\=(true),TermsS,TermsF),
    predsort(fml_compare,TermsF,Terms),
    (
        member(false,Terms) -> S=false
    ;
        length(Terms,0) -> S=true
    ;
        pairfrom(Terms,F1,F2), struct_oppos(F1,F2) -> S=false
    ;
        joinlist('&',Terms,S)
    ).
simplify(P | Q,S) :-
    flatten_op('|',[P,Q],TermsT),
    maplist(simplify,TermsT,TermsS),
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
simplify(P -> Q,S) :-
    simplify(P,Sp),
    simplify(Q,Sq),
    (
        Sp=false -> S=true
    ;
        Sp=true -> S=Sq
    ;
        Sq=true -> S=true
    ;
        Sq=false -> S=(-Sp)
    ;
        S = (Sp -> Sq)
    ).
simplify(P <-> Q,S) :-
    simplify(P,Sp),
    simplify(Q,Sq),
    (
        struct_equiv(P,Q) -> S=true
    ;
        struct_oppos(P,Q) -> S=false
    ;
        Sp=false -> S=(-Sq)
    ;
        Sq=true -> S=Sq
    ;
        Sq=false -> S=(-Sp)
    ;
        Sq=true -> S=Sp
    ;
        S = (Sp <-> Sq)
    ).
simplify(-P,S) :-
    simplify(P,SP),
    (
        SP=false -> S=true
    ;
        SP=true -> S=false
    ;
        SP = -P2 -> S=P2
    ;
        S = -SP
    ).
simplify(all(Xs,P),S) :-
    ( Xs = [] -> simplify(P,S)
    ;
    flatten_quant_and_simp('all',P,Xs,VarsT,Body),
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
              S2=all(Vars2,Body2)
            ;
              joinlist('|',Indep,IndepB),
              S2=(all(Vars2,Body2) | IndepB)
            )

          ; flatten_op('&',[Body],BTerms), BTerms = [_,_|_] ->
            split_matching(BTerms,indep_of_vars(Vars),Indep,BT2),
            joinlist('&',BT2,Body2),
            ( Indep = [] ->
              S2=all(Vars2,Body2)
            ;
              joinlist('&',Indep,IndepB),
              S2=(all(Vars2,Body2) | IndepB)
            )
          ;
            S2=all(Vars2,Body)
          )
        ),
        S = S2
    )).
simplify(exists(Xs,P),S) :-
   ( Xs = [] -> simplify(P,S)
   ;
   flatten_quant_and_simp('exists',P,Xs,VarsT,Body),
   sort(VarsT,Vars),
   (
       Body=false -> S=false
   ;
       Body=true -> S=true
   ;
       % Remove vars that are assigned a specific value, therefore useless
       flatten_op('&',[Body],Cs), member((T1=T2),Cs),
       (
           vmember(T1:_,Vars),(\+ vmember(T2:_,Vars)),
           vdelete(Vars,T1:_,Vars2), T1=T2
       ;
           vmember(T2:_,Vars),(\+ vmember(T1:_,Vars)),
           vdelete(Vars,T2:_,Vars2), T2=T1
       ;
           vmember(T1:_,Vars), vmember(T2:_,Vars), T1 \== T2,
           vdelete(Vars,T1:_,Vars2) , T1=T2
       )
           ->  simplify(exists(Vars2,Body),S)
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
             S = exists(Vars2,Body2)
           ;
             joinlist('|',Indep,IndepB),
             S = (exists(Vars2,Body2) | IndepB)
           )
         ; flatten_op('&',[Body],BTerms), BTerms = [_,_|_] ->
           split_matching(BTerms,indep_of_vars(Vars),Indep,BT2),
           joinlist('&',BT2,Body2),
           ( Indep = [] ->
             S = exists(Vars2,Body2)
           ;
             joinlist('&',Indep,IndepB),
             S = (exists(Vars2,Body2) | IndepB)
           )
         ;
           S=exists(Vars2,Body)
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
fml2nnf(P <-> Q,N) :-
    fml2nnf((P -> Q) & (Q -> P),N), !.
fml2nnf(P -> Q,N) :-
    fml2nnf((-P) | Q,N), !.
fml2nnf(-(P & Q),N) :-
   fml2nnf((-P) | (-Q),N), !.
fml2nnf(-(P | Q),N) :-
   fml2nnf((-P) & (-Q),N), !.
fml2nnf(-(all(X,P)),N) :-
   fml2nnf(exists(X,-P),N), !.
fml2nnf(-(exists(X,P)),N) :-
   fml2nnf(all(X,-P),N), !.
fml2nnf(-(-P),N) :-
    fml2nnf(P,N), !.
fml2nnf(P & Q,Np & Nq) :-
    fml2nnf(P,Np), fml2nnf(Q,Nq), !.
fml2nnf(P | Q,Np | Nq) :-
    fml2nnf(P,Np), fml2nnf(Q,Nq), !.
fml2nnf(all(X,P),all(X,N)) :-
    fml2nnf(P,N), !.
fml2nnf(exists(X,P),exists(X,N)) :-
    fml2nnf(P,N), !.
fml2nnf(P,P).


%
%  is_literal(P)  -  the formula P is a literal, not a compound expression
%
is_literal(P) :-
    P \= (-_),
    P \= (_ & _),
    P \= (_ | _),
    P \= (_ -> _),
    P \= (_ <-> _),
    P \= exists(_,_),
    P \= all(_,_).

%
%  rename_vars(Vars,F,NewVars,NewF)  -  rename the given variables to new
%                                       ones, producing a modified formula.
rename_vars([],P,[],P).
rename_vars([X:D|Xs],P,[V:D|Vs],Q) :-
    subs(X,V,P,Pt),
    rename_vars(Xs,Pt,Vs,Q).

    
%
%  terms_in_fml(F,Terms)  -  list all the basic terms found in the formula
%
terms_in_fml(P,Terms) :-
    is_literal(P), !,
    P =.. [_|Args],
    sublist(ground,Args,TermsT),
    sort(TermsT,Terms).
terms_in_fml(-P,Terms) :-
    !, terms_in_fml(P,Terms).
terms_in_fml(CP,Terms) :-
    CP =.. [Op,P1,P2],
    memberchk(Op,['&','|','->','<->']), !,
    terms_in_fml(P1,T1),
    terms_in_fml(P2,T2),
    oset_union(T1,T2,Terms).
terms_in_fml(CP,Terms) :-
    CP =.. [Q,_,P],
    memberchk(Q,[all,exists]),
    terms_in_fml(P,Terms).



%
%  In conjunction with this file, one requires an implementation of actual
%  logical reasoning.  Such a reasoning engine, like this file, must enforce
%  unique names axioms for all ground terms in formulae - that is, for any
%  terms returned by terms_in_fml/2.
%
%  The following predicates are expected to be provided by an implementation
%  of logical reasoning.
%
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

