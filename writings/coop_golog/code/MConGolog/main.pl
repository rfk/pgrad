
%  Constraint solving library.  It's possible to solve over both
%  reals (r) or rationals (q).  Rationals are used for the time being
%  as it allows the solver to substitue precise values for solved variables.
%:- use_package(clpr).
:- use_package(clpq).


%  Useful prolog predicates
:- use_module(library(aggregates)).
:- use_module(library(iso_misc)).
:- use_module(library(lists)).

:- use_module(library('clpq/solver_q')).
:- use_module(library('clpq/eval_q')).
:- use_package(library('clpqr-common/simplex')).

:- discontiguous trans/4, final/2, prim_action/1, natural/1, poss/3,
                 conflicts/3, start/2.

%%  Syntactic operators for MConGolog programs
:- op(660,xfy,/).  % Nondeterministic choice
:- op(650,xfy,:).  % Sequence
:- op(640,xfy,//). % Concurrent execution
:- op(640,xfy,>>). % Prioritised concurrency
:- op(620,fx,?).  % Test

:- include(mcongolog).
:- include(sitcalc).
:- include(domain).


main(_) :-
    do(control,s0,S), display(S).

main :-
    main(_).
