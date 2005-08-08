
%%  Syntactic operators for MConGolog programs
%%  Defined here to make get them to work.
:- op(660,xfy,|).  % Nondeterministic choice
:- op(650,xfy,:).  % Sequence
:- op(640,xfy,//). % Concurrent execution
:- op(640,xfy,>>). % Prioritised concurrency
:- op(620,fx,?).  % Test

:- lib(ic).

:- set_flag(all_dynamic,on).

:- [mcongolog].
:- [sitcalc].
:- [domain].


