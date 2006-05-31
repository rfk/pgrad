

:- dynamic holds_memo_t/2.
:- dynamic holds_memo_f/2.


literal(F) :-
    F \= and(_,_), F \= or(_,_), F \= neg(_), F \= all(_,_), F \= some(_,_),
    F \= true, F \= false.

holds(true,_) :- !.

holds(false,_) :- !, fail.

holds(and(F1,F2),S) :-
    holds(F1,S),
    holds(F2,S).

holds(or(F1,F2),S) :-
    holds(F1,S)
    ; holds(F2,S).

holds(all(V,F),S) :-
    holds(neg(some(V,neg(F))),S).

holds(some(V,F),S) :-
    sub(V,_,F,Fr), holds(Fr,S).

holds(neg(neg(F)),S) :-
    holds(F,S).

holds(neg(and(F1,F2)),S) :-
    holds(or(neg(F1,neg(F2))),S).

holds(neg(or(F1,F2)),S) :-
    holds(and(neg(F1),neg(F2)),S).

holds(neg(all(V,F)),S) :-
    holds(some(V,neg(F)),S).

holds(neg(some(V,F)),S) :-
    \+ holds(some(V,F),S).

holds(neg(F),S) :-
    literal(F), \+ holds(F,S).

holds(F,do(A,S)) :-
    literal(F),
    ground(F), ground(A), ground(S),
    ( holds_m(F,do(A,S)) ->
        assert(holds_memo_t(F,do(A,S)))
    ;
        assert(holds_memo_f(F,do(A,S))),
        fail
    ), !.

holds(F,do(A,S)) :-
    literal(F),
    holds_m(F,do(A,S)).

holds_m(F,do(A,S)) :-
    holds_memo_t(F,do(A,S))
    ;
    ( ground(F), ground(A), ground(S) ->
        \+ holds_memo_f(F,do(A,S))
    ; true
    ),
    (
    causes_true(A,F,P), holds(P,S)
    ;
    holds(F,S), \+ (causes_false(A,F,P), holds(P,S))
    ).


holds_memo_t(true,_).
holds_memo_f(false,_).

sub(_,_,T,Tr) :-
    var(T), Tr = T.
sub(X,Y,T,Tr) :-
    \+ var(T), T = X, Tr = Y.
sub(X,Y,T,Tr) :-
    T \= X, T =.. [F|Ts], sub_list(X,Y,Ts,Trs), Tr =.. [F|Trs].

sub_list(_,_,[],[]).
sub_list(X,Y,[T|Ts],[Tr|Trs]) :-
    sub(X,Y,T,Tr), sub_list(X,Y,Ts,Trs).



prim_action(pickup(O)) :-
    prim_object(O).
prim_action(drop(O)) :-
    prim_object(O).
prim_action(wait).

prim_fluent(holding(O)) :-
    prim_object(O).

prim_object(O) :-
    member(O,[block1,block2,block3]).

causes_true(pickup(X),holding(X),true).
causes_false(drop(X),holding(X),true).


list_to_sit([],s0).
list_to_sit([H|T],do(H,S)) :-
    list_to_sit(T,S).

random_situation(0,s0).
random_situation(N,do(A,S)) :-
    N > 0,
    random_action(A),
    N2 is N - 1,
    random_situation(N2,S).

random_action(A) :-
    findall(I,prim_action(I),As),
    random_member(As,A).
    
random_member(L,I) :-
    length(L,N),
    R is (random(N-1)),
    nth0(R,L,I).

