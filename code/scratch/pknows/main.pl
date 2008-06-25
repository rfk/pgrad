
:- multifile(adp_fluent/3).
:- index(adp_fluent(1,1,0)).

:- multifile(constraint/1).

:- discontiguous(causes_true/3).
:- discontiguous(causes_false/3).

:- set_prolog_flag(double_quotes,atom).

:- use_module(library(plunit)).

:- [fluent].
:- [pred_e].
:- [domain].
:- [sitcalc].
:- [pcond].

main :-
  write('\\documentclass{article}'), nl,
  write('\\usepackage{amsmath}'), nl,
  write('\\begin{document}'), nl,
  nl, nl,
  P = ~holding(max,box1),
  write_eqn(P),
  nl, nl,
  pcond_d1(P,pbu(sam),Pd1),
  write_eqn(Pd1),
  nl, nl,
  write('\\end{document}').

