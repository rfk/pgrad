%%
%%  main.pl:  Top-level prolog file for ConGolog implementation
%%
%%  Author:  Ryan Kelly (rfk)
%%
%%  Date Created:  12/03/07
%%
%%    This file is the entry-point for an ConGolog program consistint
%%    of the following files:
%%
%%      * Axioms of the situation calculus, in sitcalc.pl
%%      * The ConGolog semantics, from congolog.pl
%%      * A domain axiomatisation, from domain.pl
%%
%%    It imports the necessary prolog libraries and performs other
%%    initialisation tasks.  It also provides the predicate main/1
%%    which may be called to execute the ConGolog procedure named
%%    'control'.
%%

:- discontiguous trans/4, final/2, prim_action/1, natural/1, poss/3,
                 conflicts/3, start/2.

%%
%%  Provide Syntactic operators for ConGolog programs
%%
:- op(660,xfy,/).  % Nondeterministic choice
:- op(650,xfy,:).  % Sequence
:- op(640,xfy,//). % Concurrent execution
:- op(640,xfy,>>). % Prioritised concurrency
:- op(620,fx,?).   % Test

%%
%%  Include the relevant definitions
%%
:- include(congolog).
:- include(sitcalc).
:- include(domain).


%%
%%  main(Args):  main entry-point for program execution
%%
%%  This predicate is designed as the entry-point for the program,
%%  it calls the MIndiGolog procedure "control" in an off-line manner.
%%
main(Args) :-
    ( length(Args,0) ->
        do(control,s0,S), nl, show_action_history(S), nl
    ;
        nl, display('ERROR: No arguments can be given'), nl
    ).

