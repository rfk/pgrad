%	$Id: unify.pl,v 2.0 1994/08/04 13:36:40 posegga Exp $	


%%% Sound unification algorithm with occurs check
%%% This should be coded in a lower-level language for efficiency.

%%% taken from:
	
%%% PTTP-IN-PROLOG-2E.PL
%%%
%%%
%%%    A Prolog Technology Theorem Prover
%%%
%%%             Mark E. Stickel
%%%





:- module(unify,[unify/2]).

		  


unify(X,Y) :-
        var(X) ->
                (var(Y) ->
                        X = Y;
                %true ->
                        functor(Y,_,N),
                        (N = 0 ->
                                true;
                        N = 1 ->
                                arg(1,Y,Y1), not_occurs_in(X,Y1);
                        %true ->
                                not_occurs_in_args(X,Y,N)),
                        X = Y);
        var(Y) ->
                functor(X,_,N),
                (N = 0 ->
                        true;
                N = 1 ->
                        arg(1,X,X1), not_occurs_in(Y,X1);
                %true ->
                        not_occurs_in_args(Y,X,N)),
                X = Y;
        %true ->
                functor(X,F,N),
                functor(Y,F,N),
                (N = 0 ->
                        true;
                N = 1 ->
                        arg(1,X,X1), arg(1,Y,Y1), unify(X1,Y1);
                %true ->
                        unify_args(X,Y,N)).

unify_args(X,Y,N) :-
        N = 2 ->
                arg(2,X,X2), arg(2,Y,Y2), unify(X2,Y2),
                arg(1,X,X1), arg(1,Y,Y1), unify(X1,Y1);
        %true ->
                arg(N,X,Xn), arg(N,Y,Yn), unify(Xn,Yn),
                N1 is N - 1, unify_args(X,Y,N1).

not_occurs_in(Var,Term) :-
        Var == Term ->
                fail;
        var(Term) ->
                true;
        %true ->
                functor(Term,_,N),
                (N = 0 ->
                        true;
                N = 1 ->
                        arg(1,Term,Arg1), not_occurs_in(Var,Arg1);
                %true ->
                        not_occurs_in_args(Var,Term,N)).

not_occurs_in_args(Var,Term,N) :-
        N = 2 ->
                arg(2,Term,Arg2), not_occurs_in(Var,Arg2),
                arg(1,Term,Arg1), not_occurs_in(Var,Arg1);
       %true ->
                arg(N,Term,ArgN), not_occurs_in(Var,ArgN),
                N1 is N - 1, not_occurs_in_args(Var,Term,N1).




