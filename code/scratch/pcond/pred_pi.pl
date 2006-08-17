%
%  pred_pi.pl:  logical reasoning based on prime implicants
%
%  This file implements the logical reasoning predicates expected by
%  fml.pl using a propositional approximation of the (finite domain)
%  first order formulae, and solving the resulting problems using
%  prime implicants.
%


%
%  fml2axioms(Fml,Axs):  Convert formula to more efficient form
%
%  This predicate is used to convert the formula in Fml into a opaque
%  form that can be used for efficient reasoning by this module. This
%  implementation produces a list of prime implicants for the formula.
%

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
        %P=Ps,
        nnf2cls(Ps,Cs)
    ;
        V = [(X:D)|Vs],
        var_subs(X,D,Vs,P,Pts,Vq),
        joinlist('&',Pts,Ps),
        simplify(Ps,P2),
        %P2=Ps,
        nnf2cls(all(Vq,P2),Cs)
    ).
nnf2cls(exists(V,P),Cs) :-
    ( V = [] ->
        simplify(P,Ps),
        %P=Ps,
        nnf2cls(Ps,Cs)
    ;
        V = [X:D|Vs],
        var_subs(X,D,Vs,P,Pts,Vq),
        joinlist('|',Pts,Ps),
        simplify(Ps,P2),
        %P2=Ps,
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
%  This is severely complicted by the fact that the find-all-solutions
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
    

