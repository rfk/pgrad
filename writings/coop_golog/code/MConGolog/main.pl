%%
%%  main.pl:  Top-level prolog file for MConGolog
%%
%%  Author:  Ryan Kelly (rfk)
%%
%%  Date Created:  28/07/05
%%
%%    This file is the entry-point for an MConGolog program consistint
%%    of the following files:
%%
%%      * Axioms of the Concurrent, Temporal Situation Calculus with
%%        Natural Actions, from sitcalc.pl
%%      * The MConGolog semantics, from mcongolog.pl
%%      * A domain axiomatisation, from domain.pl
%%
%%    It imports the necessary prolog libraries and performs other
%%    initialisation tasks.  It also provides the predicate main/1
%%    which may be called to execute the MConGolog procedure named
%%    'control' in an off-line fashion.
%%

%%
%%  Load an appropriate constraint solving library.
%%
%%  Ciao provides linear constraint solving over the reals (clpr) and
%%  rationals (clpq).  For the moment clpq is being used, as it seems
%%  to allow the solver to infer the values of variables which have been
%%  constrained to a constant value.
%%
%%  Several supporting libraries are also loaded which allow the
%%  constraints to be solved, reducing them to a ground instantiation.
%%
:- use_package(clpq).
:- use_module(library('clpq/solver_q')).
:- use_module(library('clpq/eval_q')).
:- use_package(library('clpqr-common/simplex')).


%%
%%  Load useful prolog predicates
%%
%%  The Ciao core is designed as a streamlined version of ISO-prolog,
%%  so several useful bits of functionality must be explicitly loaded.
%%
:- use_module(library(aggregates)).
:- use_module(library(iso_misc)).
:- use_module(library(lists)).

:- discontiguous trans/4, final/2, prim_action/1, natural/1, poss/3,
                 conflicts/3, start/2.

%%
%%  Provide Syntactic operators for MConGolog programs
%%
%%  These operators form the "syntactic sugar" for MConGolog programs
%%
:- op(660,xfy,/).  % Nondeterministic choice
:- op(650,xfy,:).  % Sequence
:- op(640,xfy,//). % Concurrent execution
:- op(640,xfy,>>). % Prioritised concurrency
:- op(620,fx,?).   % Test

%%
%%  Include the relevant definitions
%%
:- include(mcongolog).
:- include(sitcalc).
:- include(domain).


%%
%%  main(Args):  main entry-point for program execution
%%
%%  This predicate is designed as the entry-point for the program,
%%  it calls the MConGolog procedure "control" in an off-line manner.
%%
main(Args) :-
    ( length(Args,0) ->
        nl, ol_do(control,s0), nl
    ;
        nl, display('ERROR: No arguments can be given'), nl
    ).

