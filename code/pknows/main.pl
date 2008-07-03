
:- set_prolog_flag(double_quotes,atom).

:- use_module(library(plunit)).

:- [fluent].
:- [epath].
:- [pred_twb].
:- [sitcalc].
:- [domain].

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


