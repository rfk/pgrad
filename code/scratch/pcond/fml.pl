%
%  fml.pl:  predicates for handling logical formulae
%
%  This file supplies the basic predicates for manipulating logical
%  formulae.  These formulae will typically be used to represent
%  fluents, but I've tried to keep it as general as possible. The
%  only thing I'm enforcing is the unique names assumption (just
%  like prolog).
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
    P = -P1, struct_equiv(P1,Q)
    ;
    Q = -Q1, struct_equiv(P,Q1)
    ;
    P=true, Q=false
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
%  contains(A,B)  -  formula A contains variable B
%
%  ncontains(A,B)  -  formula A does not contain variable B
%

%  Since we know that B is a variable, we do this test by grounding
%  it then checking for structural equivalence with the original term
contains(A,B) :-
    \+ ncontains(A,B).

ncontains(A,B) :-
    copy_term(A^B,A2^B2),
    B2=groundme,
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
%  vmember(Elem,List) - like member/2, but specific to our quant variable lists
%
vmember(_,[]) :- fail.
vmember(E:V,[H:U|T]) :-
    V=U, E == H
    ;
    vmember(E:V,T).


%  vdelete(List,Elem,Result) - like delete/3 but for quant variable lists
vdelete([],_,[]).
vdelete([H:U|T],E:V,Res) :-
    ( V=U, E == H ->
        vdelete(T,E:V,Res)
    ;
        Res = [H:U|T2],
        vdelete(T,E:V,T2)
    ).

%
%  simplify(+F1,-F2) - simplify a formula
%  
%  This predicate applies some basic simplification rules to a formula
%  to eliminate redundancy and (hopefully) speed up future reasoning.
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
        member(F1,Terms), member(F2,Terms), struct_oppos(F1,F2) -> S=false
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
        member(F1,Terms), member(F2,Terms), struct_oppos(F1,F2) -> S=true
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
simplify(all([],P),S) :-
    simplify(P,S).
simplify(all([H|T],P),S) :-
    flatten_quant('all',P,[H|T],VarsT,BodyP),
    sort(VarsT,Vars),
    simplify(BodyP,Body),
    (
        functor(Body,'all',2) -> simplify(all(Vars,Body),S)
    ;
        Body=false -> S=false
    ;
        Body=true -> S=true
    ;
        % Remove any useless variables
        member(X2:_,Vars), ncontains(Body,X2) ->
            vdelete(Vars,X2:_,Vars2), simplify(all(Vars2,Body),S)
    ;
        % Push independent components outside the quantifier,
        flatten_op('|',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
        \+ ( member(X2:_,Vars), contains(T,X2) ) ->
             delete(BTerms,T,BT2),
             joinlist('|',BT2,Body2),
             simplify(all(Vars,Body2) | T,S)
        
    ;
        flatten_op('&',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
        \+ ( member(X2:_,Vars), contains(T,X2) ) ->
            delete(BTerms,T,BT2),
            joinlist('&',BT2,Body2),
            simplify(all(Vars,Body2) & T,S)
    ;
        S=all(Vars,Body)
    ).
simplify(exists([],P),S) :-
    simplify(P,S).
simplify(exists([H|T],P),S) :-
   flatten_quant('exists',P,[H|T],VarsT,BodyP),
   sort(VarsT,Vars),
   simplify(BodyP,Body),
   (
       functor(Body,exists,2) -> simplify(exists(Vars,Body),S)
   ;
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
       % Remove vars not involved in the body
       member(X2:_,Vars), ncontains(Body,X2) ->
           vdelete(Vars,X2:_,Vars2), simplify(exists(Vars2,Body),S)
   ; 
       % Push independent components outside the quantifier
       flatten_op('|',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
       \+ ( member(X2:_,Vars), contains(T,X2) ) ->
           vdelete(BTerms,T,BT2),
           joinlist('|',BT2,Body2),
           simplify(exists(Vars,Body2) | T,S)
    ;
       flatten_op('&',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
       \+ ( member(X2:_,Vars), contains(T,X2) ) ->
           vdelete(BTerms,T,BT2),
           joinlist('&',BT2,Body2),
           simplify(exists(Vars,Body2) & T,S)
    ;
       S=exists(Vars,Body)
    ).
simplify((A=B),S) :-
   (
       A == B -> S=true
   ;
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
%  fml2axioms(Fml,Axs):  Convert formula to more efficient form
%
%  This predicate is used to convert the formula in Fml into a opaque
%  for that can be used for efficient reasoning by this module.
%

% Our implementation is based on prime implicants
fml2axioms(Fml,Axs) :-
    fml2cls(Fml,Cls),
    prime_implicants(Cls,Axs).

add_to_axioms(Fml,Axs,Axs2) :-
    fml2cls(Fml,Cls),
    pi_step(Cls,Axs,Axs2).

combine_axioms(Ax1,Ax2,Axs) :-
    pi_step(Ax1,Ax2,Axs).

pi_step([],PIs,PIs).
pi_step([C|Cs],Ax,PIs) :-
    ( (member(C2,Ax), subset(C2,C) ) ->
        % If the clause is subsumed, just discard it
        pi_step(Cs,Ax,PIs)
    ; 
        % Find the any resolvents and add them to the list
        pi_resolvents(C,Ax,Rs),
        append(Rs,Cs,Cs2),
        % Remove any clauses subsumed by C
        sublist(nsubset(C),Ax,Ax2),
        % Recurse!
        pi_step(Cs2,[C|Ax2],PIs)
    ).

resolvent(C1,C2,R) :-
    member(A,C1), member(-A,C2),
    oset_delel(C1,A,C1t), oset_delel(C2,-A,C2t),
    oset_union(C1t,C2t,R).
resolvent(C1,C2,R) :-
    member(-A,C1), member(A,C2),
    oset_delel(C1,-A,C1t), oset_delel(C2,A,C2t),
    oset_union(C1t,C2t,R).

pi_resolvents(C,Cs,Rs) :-
    findall(R,Ct^(member(Ct,Cs), resolvent(Ct,C,R), \+tautology_clause(R)),Rs).

nsubset(C,D) :-
    \+ subset(C,D).

%
%  prime_implicants(Cls,PIs):  calculate prime implicants of a clause set
%

prime_implicants(Cls,PIs) :-
    pi_step(Cls,[],PIs).


%
%  entails(Axioms,Conc):  Conc is logically entailed by Axioms
%
%  Axioms must be a list.
%


entails(Axioms,Conc) :-
    copy_term(Conc,Conc2),
    fml2cls(Conc2,Clauses),
    entails_clauses(Axioms,Clauses).


rename_vars([],P,[],P).
rename_vars([X:D|Xs],P,[V:D|Vs],Q) :-
    subs(X,V,P,Pt),
    rename_vars(Xs,Pt,Vs,Q).
    


entails_clauses(_,[]).
entails_clauses(PIs,[C|Cs]) :-
    pi_entails(PIs,C),
    entails_clauses(PIs,Cs).

tautology_clause(C) :-
    memberchk(true,C), !.
tautology_clause(C) :-
    member(A,C), member(-A,C), !.

pi_entails([],_) :- fail.
pi_entails([PI|PIs],C) :-
    ( subset(PI,C) ->
       true
    ;
       pi_entails(PIs,C)
    ).

is_literal(P) :-
    P \= (-_),
    P \= (_ & _),
    P \= (_ | _),
    P \= (_ -> _),
    P \= (_ <-> _),
    P \= exists(_,_),
    P \= all(_,_).

fml2cls(F,Cs) :-
    normalize(F,Fn),
    fml2nnf(Fn,N),
    nnf2cls(N,Cst),
    sublist(ntaut,Cst,Cs).

elim_quants(Q,F) :-
    fml2cls(Q,Cs),
    maplist(joinlist('|'),Cs,Ors),
    joinlist('&',Ors,F).

ntaut(C) :-
    \+ tautology_clause(C).

% we use the transformation to NNF to eliminate <-> and -> for us,
% and to ensure that negation is always at a literal.
nnf2cls(P,[[P]]) :-
    is_literal(P).
nnf2cls(-P,[[-P]]).
nnf2cls(all(V,P),Cs) :-
    ( V = [] ->
        simplify(P,Ps),
        nnf2cls(Ps,Cs)
    ;
        V = [(X:D)|Vs],
        var_subs(X,D,Vs,P,Pts,Vq),
        joinlist('&',Pts,Ps),
        simplify(Ps,P2),
        nnf2cls(all(Vq,P2),Cs)
    ).
nnf2cls(exists(V,P),Cs) :-
    ( V = [] ->
        simplify(P,Ps),
        nnf2cls(Ps,Cs)
    ;
        V = [X:D|Vs],
        var_subs(X,D,Vs,P,Pts,Vq),
        joinlist('|',Pts,Ps),
        simplify(Ps,P2),
        nnf2cls(exists(Vq,P2),Cs)
    ).
nnf2cls(P & Q,Cs) :-
    nnf2cls(P,Cp),
    nnf2cls(Q,Cq),
    oset_union(Cp,Cq,Cs).
nnf2cls(P | Q,Cs) :-
    nnf2cls(P,Cp),
    nnf2cls(Q,Cq),
    findall(U,C1^C2^(member(C1,Cp), member(C2,Cq), oset_union(C1,C2,U)),Cst),
    sort(Cst,Cs).
 

%
%  var_subs(X,D,V,P,Px,Vq) - substitute variable for elements from its domain
%
%  This predicate takes a variable X, its domain D, and a formula P, and
%  produces a list of formulae Px such that each member of the list is an
%  instance of P with the variable X substituted for a different value from
%  the domain.  V is a list of other variable names to be preserved, abd
%  Vq will be bound to an equivalent list of new variables.
%
%  Tis is severely complicted by the fact that the find-all-solutions
%  procedure introduces new variables for any free variables in the goal.
%  This is usually the right thing, but not for our purposes...
%
var_subs(X,D,Vs,P,Px,Vq) :-
    assert(var_subs_a([X^P],Vs)),
    var_subs_aux(D,Px,Vq).

var_subs_aux(D,Px,Vq) :-
    call(D,V),
    retract(var_subs_a([X^P|Ls],Vt)),
    subs(X,V,P,P2),
    assert(var_subs_a([X^P,P2|Ls],Vt)),
    fail
    ;
    retract(var_subs_a([_|Px],Vq)).
    

terms_in_fml(P,Terms) :-
    is_literal(P),
    P =.. [_|Args],
    sublist(ground,Args,TermsT),
    sort(TermsT,Terms).
terms_in_fml(-P,Terms) :-
    terms_in_fml(P,Terms).
terms_in_fml(CP,Terms) :-
    CP =.. [Op,P1,P2],
    memberchk(Op,['&','|','->','<->']),
    terms_in_fml(P1,T1),
    terms_in_fml(P2,T2),
    oset_union(T1,T2,Terms).
terms_in_fml(CP,Terms) :-
    CP =.. [Q,_,P],
    memberchk(Q,[all,exists]),
    terms_in_fml(P,Terms).

