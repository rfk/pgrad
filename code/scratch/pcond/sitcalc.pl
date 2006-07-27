

action_term(pickup(_,_)).
action_term(putdown(_,_)).
action_term(drop(_,_)).

fml_compare('=',F1,F2) :-
    struct_equiv(F1,F2), !.
fml_compare(Ord,F1,F2) :-
    ( F1 @< F2 ->
        Ord = '<'
    ;
        Ord = '>'
    ).


reallysimplify(P,S) :-
    rs_aux([],P,S).

rs_aux(Prevs,C,S) :-
    member(C2,Prevs), C2 =@= C, C=S, !.
rs_aux(Prevs,Cur,Simp) :-
    normalize(Cur,Norm),
    fml2qlf(Norm,Cur2),
    rs_aux([Cur|Prevs],Cur2,Simp).

normalize((A=B),(A=B)) :-
    A @< B, !.
normalize((A=B),(B=A)) :-
    B @< A, !.
normalize((A=B),true) :-
    A == B, !.
normalize(exists(X,P),exists(X,Q)) :-
    normalize(P,Q), !.
normalize(all(X,P),all(X,Q)) :-
    normalize(P,Q), !.
normalize(-P,-Q) :-
    normalize(P,Q), !.
normalize((P1 & Q1),(P2 & Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize((P1 | Q1),(P2 | Q2)) :-
    normalize(P1,P2),
    normalize(Q1,Q2), !.
normalize(P,P). 

struct_equiv(P,Q) :-
    P =@= Q.

struct_oppos(P,Q) :-
    P = -P1, struct_equiv(P1,Q)
    ;
    Q = -Q1, struct_equiv(P,Q1).


flatten_terms(O,Ts,Res) :-
    flatten_terms(O,Ts,[],Res).

flatten_terms(_,[],Res,Res).
flatten_terms(O,[T|Ts],Acc,Res) :-
    ( T =.. [O|Args] ->
        append(Args,Ts,Ts2),
        flatten_terms(O,Ts2,Acc,Res)
    ;
        flatten_terms(O,Ts,[T|Acc],Res)
    ).

flatten_quants(Q,T,Vars,Vars,T) :-
    \+ functor(T,Q,2), !.
flatten_quants(Q,T,Acc,Vars,Body) :-
    T =.. [Q,V,T2],
    flatten_quants(Q,T2,[V|Acc],Vars,Body).

listdel([],_,[]).
listdel([H|T],E,L) :-
    ( H == E ->
        listdel(T,E,L)
    ;
        L = [H|L2],
        listdel(T,E,L2)
    ).

expand_quants(all(X,P),E) :- 
    \+ is_list(X), expand_quants(P,E), !.
expand_quants(all([],P),E) :- 
    expand_quants(P,E), !.
expand_quants(all([H|T],P),E) :-
    E=all(H,P2),
    expand_quants(all(T,P),P2), !.
expand_quants(exists(X,P),E) :-
    \+ is_list(X), expand_quants(P,E), !.
expand_quants(exists([],P),E) :-
    expand_quants(P,E), !.
expand_quants(exists([H|T],P),E) :-
    E=exists(H,P2),
    expand_quants(exists(T,P),P2), !.
expand_quants(-P,-E) :-
    expand_quants(P,E), !.
expand_quants(P & Q,Ep & Eq) :-
    expand_quants(P,Ep),
    expand_quants(Q,Eq), !.
expand_quants(P | Q,Ep | Eq) :-
    expand_quants(P,Ep),
    expand_quants(Q,Eq), !.
expand_quants(P,P).

%
%  simplify(+F1,-F2) - simpfily a fluent expression
%  
%  This predicate applies some basic simplification rules to a fluent
%  to eliminate redundancy and (hoepfully) speed up future reasoning.
%  
simplify(P & Q,S) :-
    flatten_terms('&',[P,Q],TermsT),
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
    flatten_terms('|',[P,Q],TermsT),
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
simplify(all(X,P),S) :-
    X == [],
    simplify(P,S), !.
simplify(all(X,P),S) :-
    ( is_list(X) -> V=X ; V=[X] ),
    flatten_quants('all',P,V,Vars,BodyP),
    simplify(BodyP,Body),
    (
        functor(Body,'all',2), simplify(all(Vars,Body),S)
    ;
        Body=false, S=false
    ;
        Body=true, S=true
    ;
        member(X2,Vars), subs(X2,_,Body,Body2), Body == Body2,
        listdel(Vars,X2,Vars2), simplify(all(Vars2,Body),S)
    ;
        S=all(Vars,Body)
    ), !.
simplify(exists(X,P),S) :-
    X == [],
    simplify(P,S), !.
simplify(exists(X,P),S) :-
   ( is_list(X) -> V=X ; V=[X] ),
   flatten_quants('exists',P,V,Vars,BodyP),
   simplify(BodyP,Body),
   list_and_clauses(Body,Cs),
   (
       Vars = [], S=Body
   ;
       functor(Body,exists,2), simplify(exists(Vars,Body),S)
   ;
       member((T1=T2),Cs),
       (
           member(X2,Vars), T1 == X2, nonvar(T2), subs(X2,T2,Body,St),
           listdel(Vars,X2,Vars2), simplify(exists(Vars2,St),S)
       ;
           member(X2,Vars), T2 == X2, nonvar(T1), subs(X2,T1,Body,St),
           listdel(Vars,X2,Vars2), simplify(exists(Vars2,St),S)
       ;
           member(X2,Vars), member(X3,Vars), X2 \== X3, T1 == X2, T2 == X3,
           subs(X2,X3,Body,St),
           listdel(Vars,X2,Vars2), simplify(exists(Vars2,St),S)
       )
   ;
       (
           Body=false, S=false
       ;
           Body=true, S=true
       ;
           member(X2,Vars), subs(X2,_,Body,Body2), Body == Body2,
           listdel(Vars,X2,Vars2), simplify(exists(Vars2,Body),S)
       ;
           S=exists(Vars,Body)
       )
   ), !.
simplify((A=B),S) :-
   (
        A == B, S=true
   ;
        ground(A), ground(B), A \= B, S=false
   ;
        nonvar(A), nonvar(B),
        A =.. [FA|ArgsA],
        B =.. [FB|ArgsB],
        length(ArgsA,NA), length(ArgsB,NB),
        (
            FA \= FB, S=false
        ;
            NA \= NB, S=false
        )
   ), !.
   
simplify(P,P).


list_and_clauses(T,[T]) :-
    (var(T) ; T =.. [F|_], F\='&'), !.
list_and_clauses((A & B),Cs) :-
    list_and_clauses(A,CsA),
    list_and_clauses(B,CsB),
    append(CsA,CsB,Cs).

%
%  consequence(+[Axioms],+Conc) - Fluent Conc is a consequence of the Axioms
%
%  This predicate employs full first-order reasoning to determine whether
%  the fluent expression Conc is logically entailed by the set of fluents
%  in Axioms.
%
consequence(F,Conc) :-
    F \= [_|_], F \= [],
    consequence([F],Conc), !.
consequence(Axioms,Conc) :-
    % TODO: automatically add unique names axioms?
    findall(C,constraint(C),Cs),
    append(Axioms,[true,-false|Cs],Bg),
    eprove(Bg,Conc,yes).



%
%  joinlist(+Op,+In,-Out) - join items in a list using given operator
%

joinlist(_,[H],H) :- !.
joinlist(O,[H|T],J) :-
    T \= [],
    J =.. [O,H,TJ],
    joinlist(O,T,TJ).

%
%  eps_p(+F,?Act,?Cond) - conditions for a fluent becoming true
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made true by the action Act.
%

eps_p((_=_),_,_) :- !, fail.
eps_p(P,A,E) :-
    bagof(Et,eps_p1(P,A,Et),Ets),
    joinlist((|),Ets,E).

%
%  eps_n(+F,?Act,?Cond) - conditions for a fluent becoming false
%
%  This predicate unifies Cond with a fluent expression giving the conditions
%  under which the fluent F will be made false by the action Act.
%
eps_n((_=_),_,_) :- !, fail.
eps_n(P,A,E) :-
    bagof(Et,eps_n1(P,A,Et),Ets),
    joinlist((|),Ets,E).

%
%  eps_p1(+F,?Act,?Cond) - individual conditions for truthifying a fluent
%
%  This preciate enumerates the different ways in which the fluent F can become
%  true, which are collected by eps_p/4.
%

eps_p1((P & Q),A,E) :-
    eps_p(P,A,EP),
    ( eps_p(Q,A,EQ) ->
        E = ((EP & EQ) | (EP & Q) | (P & EQ))
    ;
      eps_n(Q,A,EQn) ->
        E = (EP & Q & -EQn)
    ;
        E = (EP & Q)
    ).
eps_p1((P & Q),A,E) :-
    eps_p(Q,A,EQ),
    ( eps_n(P,A,EPn) ->
        E = (P & -EPn & EQ)
    ;
        E = (P & EQ)
    ).

eps_p1((P | _),A,E) :-
    eps_p(P,A,E).
eps_p1((_ | Q),A,E) :-
    eps_p(Q,A,E).

eps_p1(-P,A,E) :-
    eps_n(P,A,E).

eps_p1(all(X,P),A,E) :-
    eps_p(P,A,EP),
    ( eps_n(P,A,EPn) ->
        E = all(X,((P & -EPn) | EP))
    ;
        E = all(X,P | EP)
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

eps_n1((P & Q),A,E) :-
    eps_p((-P) | (-Q),A,E).

eps_n1((P | Q),A,E) :-
    eps_p((-P) & (-Q),A,E).

eps_n1(-P,A,E) :-
    eps_p(P,A,E).

eps_n1(all(X,P),A,E) :-
    eps_p(exists(X,-P),A,E).

eps_n1(exists(X,P),A,E) :-
    eps_p(all(X,-P),A,E).

eps_n1(P,A,E) :-
    causes_false(P,A,E).

% eps_n1(B=C,A,false).   is implicit


%
%  regression(+F,+A,-Fr) - Fr is the regression of F over action A
%
%  This predicate calculates the regression of a fluent F with respect to
%  an action A, yielding a new fluent Fr.  If A is free, will consider all
%  type of action that could affect the fluent.
%

%  If A is non-free, regression1 will succeed only once.
regression(F,A,Fr) :-
    nonvar(A),
    regression1(F,A,Frt),
    simplify(Frt,Fr).

%  If A is free, find all actions which could affect it.
regression(F,A,Fr) :-
    var(A),
    (bagof(Ft,B^regression_bagof(F,A,B,Ft),Fts) ->
        joinlist((|),Fts,Ftmp),
        simplify(Ftmp,Fr)
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

regression1(F,A,Fr) :-
    eps_p(F,A,Ep),
    eps_n(F,A,En),
    simplify(Ep | (F & -En),Fr).
regression1(F,A,Fr) :-
    eps_p(F,A,Ep), 
    \+ eps_n(F,A,_),
    simplify(Ep | F,Fr).
regression1(F,A,Fr) :-
    eps_n(F,A,En), 
    \+ eps_p(F,A,_),
    simplify(F & -En,Fr).
regression1(F,A,Fr) :-
    \+ eps_n(F,A,_), 
    \+ eps_p(F,A,_),
    F = Fr.

%
%  holds(+F,+S) - fluent F holds in situation S
%
%  This predicate is true whenever the fluent F holds in situation S.
%
holds(true,_).
holds(A=B,_) :-     % no functional fluents, so equality does not vary
    A=B.
holds(-(A=B),_) :-
    A \= B.
holds(F,do(A,S)) :-
    regression(F,A,Fr),
    holds(Fr,S).
holds(F1 & F2,s0) :-
    holds(F1,s0), holds(F2,s0).
holds(F1 | F2,s0) :-
    holds(F1,s0) ; holds(F2,s0).
holds(all(V,F),s0) :-
    holds(-exists(V,-F),s0).
holds(exists(V,F),s0) :-
    %subs(V,_,F,F1), holds(F1,s0).
    holds(F,s0).
holds(-(F1 & F2),s0) :- 
    holds((-F1) | (-F2),s0).
holds(-(F1 | F2),s0) :-
    holds((-F1) & (-F2),s0).
holds(-all(V,F),s0) :-
    holds(exists(V,F),s0).
holds(-exists(V,F),s0) :-
    \+ holds(exists(V,F),s0).
holds(F,s0) :-
    prim_fluent(F), 
    initially(F).
holds(-F,s0) :-
    prim_fluent(F),
    \+ initially(F).

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
%  This predicate operates as sub/4, but Old and New are lists of terms
%  instead of single terms.  Basically, it calls sub/4 recursively on
%  each element of the list.
%
subs_list(_,_,[],[]).
subs_list(X,Y,[T|Ts],[Tr|Trs]) :-
    subs(X,Y,T,Tr), subs_list(X,Y,Ts,Trs).


knows(Agt,F,[]) :-
    pcond(F,legObs(Agt),P),
    holds(P,s0).
knows(Agt,F,[A|T]) :-
    pcond(F,legObs(Agt),P),
    regression(P,A,R),
    adp_fluent(poss,A,Poss),
    knows(agt,(-Poss | R),T).


equiv(P,Q) :-
    consequence(P,Q), consequence(Q,P).



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

rename_vars(all(X,P),all(X1,P1)) :-
    subs(X,X1,P,Pt),
    rename_vars(Pt,P1), !.
rename_vars(exists(X,P),exists(X1,P1)) :-
    subs(X,X1,P,Pt),
    rename_vars(Pt,P1), !.
rename_vars(-P,-P1) :-
    rename_vars(P,P1), !.
rename_vars(P & Q,P1 & Q1) :-
    rename_vars(P,P1),
    rename_vars(Q,Q1), !.
rename_vars(P | Q,P1 | Q1) :-
    rename_vars(P,P1),
    rename_vars(Q,Q1), !.
rename_vars(P,P).

occurs_in(A,B) :-
    subs(A,X,B,B2),
    B \== B2.

nnf2qlf(all(X,P) & all(X,Q),all(X,R)) :-
    nnf2qlf(P & Q,R), !.
nnf2qlf(exists(X,P) | exists(X,Q),exists(X,R)) :-
    nnf2qlf(P | Q,R), !.
nnf2qlf(F1 & F2,F3) :-
    F1 =.. [Q1,V1,P1],
    F2 =.. [Q2,V2t,P2t],
    member(Q1,[all,exists]),
    member(Q2,[all,exists]),
    ( V1 == V2t ->
        subs(V2t,V2,P2t,P2)
    ;
        V2 = V2t, P2=P2t
    ),
    F3t =.. [Q2,V2,R],
    F3 =.. [Q1,V1,F3t],
    nnf2qlf(P1 & P2,R), !.
nnf2qlf(F1 | F2,F3) :-
    F1 =.. [Q1,V1,P1],
    F2 =.. [Q2,V2t,P2t],
    member(Q1,[all,exists]),
    member(Q2,[all,exists]),
    ( V1 == V2t ->
        subs(V2t,V2,P2t,P2)
    ;
        V2 = V2t, P2=P2t
    ),
    F3t =.. [Q2,V2,R],
    F3 =.. [Q1,V1,F3t],
    nnf2qlf(P1 | P2,R), !.
nnf2qlf(all(X,P) & Q,all(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(P & Q,R), !.
nnf2qlf(Q & all(X,P),all(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(Q & P,R), !.
nnf2qlf(all(X,P) | Q,all(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(P | Q,R), !.
nnf2qlf(Q | all(X,P),all(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(Q | P,R), !.
nnf2qlf(exists(X,P) & Q,exists(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(P & Q,R), !.
nnf2qlf(Q & exists(X,P),exists(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(Q & P,R), !.
nnf2qlf(exists(X,P) | Q,exists(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(P | Q,R), !.
nnf2qlf(Q | exists(X,P),exists(X,R)) :-
    \+ occurs_in(X,Q),
    nnf2qlf(Q | P,R), !.

nnf2qlf(all(X,P),all(X,R)) :-
    nnf2qlf(P,R), !.
nnf2qlf(exists(X,P),exists(X,R)) :-
    nnf2qlf(P,R), !.
nnf2qlf(P & Q,R) :-
    nnf2qlf(P,Rp), nnf2qlf(Q,Rq),
    ( (P \== Rp ; Q \== Rq) ->
        nnf2qlf(Rp & Rq,R)
    ;
        R = (P & Q)
    ), !.
nnf2qlf(P | Q,R) :-
    nnf2qlf(P,Rp), nnf2qlf(Q,Rq),
    ( (P \== Rp ; Q \== Rq) ->
        nnf2qlf(Rp | Rq,R)
    ;
        R = (P | Q)
    ), !.
nnf2qlf(P,P).

qlf2pnf(all(X,P),all(X,Q)) :-
    qlf2pnf(P,Q), !.
qlf2pnf(exists(X,P),exists(X,Q)) :-
    qlf2pnf(P,Q), !.
qlf2pnf(P & Q,R) :-
    qlf2pnf(P,Rp),
    qlf2pnf(Q,Rq),
    R = (Rp & Rq), !.
qlf2pnf((P | Q),R) :-
    qlf2pnf(P,Rp),
    qlf2pnf(Q,Rq),
    (
       Rp = (A & B), Rq \= (_ & _), qlf2pnf((A | Rq) & (B | Rq),R)
    ;
       Rp \= (_ & _), Rq = (A & B), qlf2pnf((Rp | A) & (Rp | B),R)
    ;
       Rp = (A & B), Rq = (C & D), qlf2pnf((A|C) & (A|D) & (B|C) & (B|D),R)
    ;
       Rp \= (_ & _), Rq \= (_ & _), R = (Rp | Rq)
    ), !.
qlf2pnf(P,P).

fml2qlf(F,Q) :-
    writeln('expanding...'),
    expand_quants(F,F1),
    writeln('renaming...'),
    rename_vars(F1,F2),
    writeln('converting...'),
    fml2nnf(F2,N),
    nnf2qlf(N,Qt),
    writeln('simplifying...'),
    simplify(Qt,Q).
 
fml2pnf(F,P) :-
    expand_quants(F,F1),
    rename_vars(F1,F2),
    fml2nnf(F2,N),
    nnf2qlf(N,Q),
    qlf2pnf(Q,P).

pnf2cls(all(X,P),C) :-
    pnf2cls(P,C), !.
pnf2cls(exists(X,P),C) :-
    pnf2cls(P,C), !.
pnf2cls(P & Q,C) :-
    pnf2cls(P,Cp),
    pnf2cls(Q,Cq),
    append(Cp,Cq,C), !.
pnf2cls(P | Q,[C]) :-
    pnf2cls(P,[Cp]),
    pnf2cls(Q,[Cq]),
    append(Cp,Cq,C), !.
pnf2cls(P,[[P]]).

simplify_cls(C,S) :-
    maplist(sort,C,Cs),
    sort(Cs,S).

