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
%  For simplicity, we expect all variables to be named 'vX' where X is
%  an integer.  We assume any other terms are objects in the domain,
%  and thus subject to UNA.
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
%  genvar(V):  generate a new, unique variable name
%
%  isvar(V):   V is a variable name, according to our conventions

genvar(V) :-
    gensym(v,V).

isvar(V) :-
    atomic(V),
    atom_concat(v,S,V),
    atom_number(S,N),
    integer(N).

notavar(V) :-
    \+ isvar(V).

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
%                        basically meaning they are identical.
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
%  contains(A,B)  -  formula A contains term B
%
%  ncontains(A,B)  -  formula A does not contain term B
%

ncontains(A,B) :-
    subs(B,_,A,Ap), A == Ap.
contains(A,B) :-
    subs(B,_,A,Ap), A \== Ap.


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
    flatten_quant(Q,T2,[V|Acc],Vars,Body).

%
%  simplify(+F1,-F2) - simplify a formula
%  
%  This predicate applies some basic simplification rules to a formula
%  to eliminate redundancy and (hopefully) speed up future reasoning.
%  
simplify(P & Q,S) :-
    flatten_op('&',[P,Q],TermsT),
    maplist(simplify,TermsT,TermsS),
    sublist(\=(true),TermsS,TermsF),
    predsort(fml_compare,TermsF,Terms),
    (
        member(false,Terms), S=false
    ;
        length(Terms,0), S=true
    ;
        member(F1,Terms), member(F2,Terms), struct_oppos(F1,F2), S=false
    ;
        joinlist('&',Terms,S)
    ), !.
simplify(P | Q,S) :-
    flatten_op('|',[P,Q],TermsT),
    maplist(simplify,TermsT,TermsS),
    sublist(\=(false),TermsS,TermsF),
    predsort(fml_compare,TermsF,Terms),
    (
        member(true,Terms), S=true
    ;
        length(Terms,0), S=false
    ;
        member(F1,Terms), member(F2,Terms), struct_oppos(F1,F2), S=true
    ;
        joinlist('|',Terms,S)
    ), !.
simplify(P -> Q,S) :-
    simplify(P,Sp),
    simplify(Q,Sq),
    (
        Sp=false, S=true
    ;
        Sp=true, S=Sq
    ;
        Sq=true, S=true
    ;
        Sq=false, S=(-Sp)
    ;
        S = (Sp -> Sq)
    ), !.
simplify(P <-> Q,S) :-
    simplify(P,Sp),
    simplify(Q,Sq),
    (
        struct_equiv(P,Q), S=true
    ;
        struct_oppos(P,Q), S=false
    ;
        Sp=false, S=(-Sq)
    ;
        Sq=true, S=Sq
    ;
        Sq=false, S=(-Sp)
    ;
        Sq=true, S=Sp
    ;
        S = (Sp <-> Sq)
    ), !.
simplify(-P,S) :-
    simplify(P,SP),
    (
        SP=false, S=true
    ;
        SP=true, S=false
    ;
        SP = -P2, S=P2
    ;
        S = -SP
    ), !.
simplify(all([],P),S) :-
    simplify(P,S), !.
simplify(all(X,P),S) :-
    flatten_quant('all',P,X,VarsT,BodyP),
    sort(VarsT,Vars),
    simplify(BodyP,Body),
    (
        functor(Body,'all',2), simplify(all(Vars,Body),S)
    ;
        Body=false, S=false
    ;
        Body=true, S=true
    ;
        % Remove any useless variables
        member(X2:_,Vars), ncontains(Body,X2),
        listdel(Vars,X2:_,Vars2), simplify(all(Vars2,Body),S)
    ;
        % Push independent components outside the quantifier,
        flatten_op('|',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
        \+ ( member(X2:_,Vars), contains(T,X2) ), delete(BTerms,T,BT2),
        joinlist('|',BT2,Body2), simplify(all(Vars,Body2) | T,S)
    ;
        flatten_op('&',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
        \+ ( member(X2,Vars), contains(T,X2) ), listdel(BTerms,T,BT2),
        joinlist('&',BT2,Body2), simplify(all(Vars,Body2) & T,S)
    ;
        S=all(Vars,Body)
    ), !.
simplify(exists([],P),S) :-
    simplify(P,S), !.
simplify(exists(X,P),S) :-
   flatten_quant('exists',P,X,VarsT,BodyP),
   sort(VarsT,Vars),
   simplify(BodyP,Body),
   (
       functor(Body,exists,2), simplify(exists(Vars,Body),S)
   ;
       Body=false, S=false
   ;
       Body=true, S=true
   ;
       % Remove vars that are assigned a specific value, therefore useless
       flatten_op('&',[Body],Cs), member((T1=T2),Cs),
       (
           member(T1:_,Vars),(\+ member(T2:_,Vars)),subs(T1,T2,Body,St),
           delete(Vars,T1:_,Vars2), simplify(exists(Vars2,St),S)
       ;
           member(T2:_,Vars),(\+ member(T1:_,Vars)),subs(T2,T1,Body,St),
           delete(Vars,T2:_,Vars2), simplify(exists(Vars2,St),S)
       ;
           member(T1:_,Vars), member(T2:_,Vars), T1 \= T2, subs(T1,T2,Body,St),
           delete(Vars,T1:_,Vars2), simplify(exists(Vars2,St),S)
       )
   ;
       % Remove vars not involved in the body
       member(X2:_,Vars), ncontains(Body,X2),
       delete(Vars,X2:_,Vars2), simplify(exists(Vars2,Body),S)
   ; 
       % Push independent components outside the quantifier
       flatten_op('|',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
       \+ ( member(X2:_,Vars), contains(T,X2) ), delete(BTerms,T,BT2),
       joinlist('|',BT2,Body2), simplify(exists(Vars,Body2) | T,S)
    ;
       flatten_op('&',[Body],BTerms), BTerms = [_,_|_], member(T,BTerms),
       \+ ( member(X2:_,Vars), contains(T,X2) ), delete(BTerms,T,BT2),
       joinlist('&',BT2,Body2), simplify(exists(Vars,Body2) & T,S)
    ;
       S=exists(Vars,Body)
    ), !.
simplify((A=B),S) :-
   (
       A = B, S=true
   ;
       \+ isvar(A), \+ isvar(B), A \= B, S=false
   ;
       S = (A=B)
   ), !.
simplify(P,P).


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
    T == X, Tr = Y.
subs(X,_,T,Tr) :-
    T \== X, var(T), T=Tr.
subs(X,Y,T,Tr) :-
    T \== X, nonvar(T), T =.. [F|Ts], subs_list(X,Y,Ts,Trs), Tr =.. [F|Trs].

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
    union(Cls,Axs,Cls2),
    prime_implicants(Cls2,Axs2).

combine_axioms(Ax1,Ax2,Axs) :-
    union(Ax1,Ax2,AxT),
    prime_implicants(AxT,Axs).

%
%  prime_implicants(Cls,PIs):  calculate prime implicants of a clause set
%


prime_implicants(Cls,PIs) :-
    ( prime_implicants_step(Cls,Cls2) ->
        prime_implicants(Cls2,PIs)
    ;
        PIs = Cls
    ).


prime_implicants_step(Cls,[R|Cls2]) :-
    member(C1,Cls),
    member(C2,Cls),
    resolvent(C1,C2,R),
    \+ (tautology_clause(R)),
    \+ (member(C3,Cls), subset(C3,R)),
    sublist(nsubset(R),Cls,Cls2).

nsubset(S1,S2) :-
    \+ subset(S1,S2).

resolvent(C1,C2,R) :-
    member(A,C1), member(-A,C2),
    delete(C1,A,C1t), delete(C2,-A,C2t),
    append(C1t,C2t,R).
resolvent(C1,C2,R) :-
    member(-A,C1), member(A,C2),
    delete(C1,A,C1t), delete(C2,-A,C2t),
    append(C1t,C2t,R).

%
%  entails(Axioms,Conc):  Conc is logically entailed by Axioms
%
%  Axioms must be a list.
%

entails(Axioms,Conc) :-
    fml2cls(Conc,Clauses),
    entails_clauses(Axioms,Clauses).

entails_clauses(_,[]).
entails_clauses(PIs,[C|Cs]) :-
    pi_entails(PIs,C),
    entails_clauses(PIs,Cs).

tautology_clause(C) :-
    memberchk(true,C), !.
tautology_clause(C) :-
    member(A,C), member(-A,C), !.
tautology_clause(C) :-
    member(A=A,C), !.

pi_entails([],_) :- fail.
pi_entails([PI|PIs],C) :-
    ( subset(PI,C) ->
       true
    ;
       pi_entails(PIs,C)
    ).

is_literal(P) :-
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

ntaut(C) :-
    \+ tautology_clause(C).

% we use the transformation to NNF to eliminate <-> and -> for us,
% and to ensure that negation is always at a literal.
nnf2cls(P,[[P]]) :-
    is_literal(P).
nnf2cls(all([],P),Cs) :-
    nnf2cls(P,Cs).
nnf2cls(all([X:D|Vs],P),Cs) :-
    findall(Pt,var_subs(X,D,P,Pt),Pts),
    joinlist('&',Pts,Ps),
    nnf2cls(all(Vs,Ps),Cs).
nnf2cls(exists([],P),Cs) :-
    nnf2cls(P,Cs).
nnf2cls(exists([X:D|Vs],P),Cs) :-
    findall(Pt,var_subs(X,D,P,Pt),Pts),
    joinlist('|',Pts,Ps),
    nnf2cls(exists(Vs,Ps),Cs).
nnf2cls(P & Q,Cs) :-
    nnf2cls(P,Cp),
    nnf2cls(Q,Cq),
    union(Cp,Cq,Cs).
nnf2cls(P | Q,Cs) :-
    nnf2cls(P,Cp),
    nnf2cls(Q,Cq),
    findall(U,C1^C2^(member(C1,Cp), member(C2,Cq), union(C1,C2,U)),Cs).
    
var_subs(X,D,P,Px) :-
    call(D,Val),
    subs(X,Val,P,Px).


terms_in_fml(P,Terms) :-
    is_literal(P), P \= (-_),
    P =.. [_|Args],
    sublist(notavar,Args,TermsT),
    sort(TermsT,Terms).
terms_in_fml(-P,Terms) :-
    terms_in_fml(P,Terms).
terms_in_fml(CP,Terms) :-
    CP =.. [Op,P1,P2],
    memberchk(Op,['&','|','->','<->']),
    terms_in_fml(P1,T1),
    terms_in_fml(P2,T2),
    union(T1,T2,Terms).
terms_in_fml(CP,Terms) :-
    CP =.. [Q,_,P],
    memberchk(Q,[all,exists]),
    terms_in_fml(P,Terms).

