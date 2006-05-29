%
%  Generate a random situation calculus domain
%


rand_integer(LB,UB,R) :-
    R is round(random(UB-LB+1) + LB).

rand_member(L,M) :-
    length(L,Nt), N is Nt - 1,
    rand_integer(0,N,R),
    nth0(R,L,M).

rand_domain(dom(Fluents,Actions)) :-
    rand_integer(10,20,NumFluents),
    rand_integer(10,20,NumActions),
    rand_func_list(fluent_,0,NumFluents,Fluents),
    rand_func_list(action_,0,NumActions,Actions).


rand_func_list(_,Max,Max,[]).
rand_func_list(Name,Min,Max,[H|T]) :-
    Min < Max,
    atom_concat(Name,Min,FName),
    rand_integer(0,4,NArgs),
    length(ArgList,NArgs),
    H =.. [FName|ArgList],
    Min2 is Min + 1,
    rand_func_list(Name,Min2,Max,T).

rand_fluent_formula(dom(Fluents,_),0,F) :-
    rand_member(Fluents,F).
rand_fluent_formula(dom(Fluents,_),Depth,F) :-
    Depth > 0,
    NewDepth is Depth - 1,
    rand_integer(0,1,R1),
    ( R1 = 1 ->
        NewDepth1 = NewDepth,
        rand_integer(0,NewDepth,NewDepth2)
    ;
        rand_integer(0,NewDepth,NewDepth1),
        NewDepth2 = NewDepth
    ),
    rand_integer(0,4,R),
    ( R = 0 ->
        F = and(F1,F2),
        rand_fluent_formula(dom(Fluents,_),NewDepth1,F1),
        rand_fluent_formula(dom(Fluents,_),NewDepth2,F2)
    ; R = 1 ->
        F = not(F2),
        rand_fluent_formula(dom(Fluents,_),NewDepth,F2)
    ; R = 2 ->
        F = or(F1,F2),
        rand_fluent_formula(dom(Fluents,_),NewDepth1,F1),
        rand_fluent_formula(dom(Fluents,_),NewDepth2,F2)
    ; R = 3 ->
        F = all(V,F2),
        rand_fluent_formula(dom(Fluents,_),NewDepth,F2)
    ; R = 4 ->
        F = ex(V,F2),
        rand_fluent_formula(dom(Fluents,_),NewDepth,F2)
    ;
        write('Shouldnt be here!'),
        fail
    ).

