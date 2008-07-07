%
%  twb_pdl.pl:  logical reasoning using the Tableaux Workbench PDL prover
%

entails(Axs,Conc) :-
    copy_term(Conc,Conc2),
    twb_pdl_prove(Axs,Conc2,yes).

twb_pdl_prove(Axioms,Conc,Result) :-
    % Create input/output files
    tmp_file(twb_in,InFile),
    tmp_file(twb_out,OutFile),
    tell(InFile),
    % Universally quantify all free variables in conc
    free_vars(Conc,ConcVars),
    ( ConcVars = [] ->
          Conc2 = Conc
    ;
          guess_var_types(ConcVars,Conc,TypedVars),
          Conc2 = !(TypedVars : Conc)
    ),
    % Write out (Axioms) -> (Conjecture)
    write('('),
    twb_write_axioms(Axioms), !,
    write(') -> ('),
    twb_write(Conc2), write(').'), nl,
    told, !,
    % Call TWB and have it write its conclusions into output file
    sformat(PCmd,'/home/rfk/twb-dev/library/pdlMark.twb < ~w > ~w',[InFile,OutFile]),
    shell(PCmd,_),
    % Grep output file for "Result:Closed" indicating truthity
    sformat(TCmd,'grep "Result:Closed" ~w > /dev/null',[OutFile]),
    ( shell(TCmd,0) ->
        Result = yes
    ;
        Result = no
    % Propositional prover, so we cannot get Result=unknown
    ).


%
%  twb_write(P)  -  write formula in TWB PDL format
%
%  All formulae are propositionalised as they are written, so we can decide
%  equality at write-time and simply write 'Verum' or 'Falsum'.
twb_write(A=B) :-
    ( A==B -> write('Verum') ; write('Falsum')).
twb_write(A\=B) :-
    ( A==B -> write('Falsum') ; write('Verum')).
twb_write(P) :-
    is_atom(P),
    P =.. [F|Terms],
    write(F),
    (Terms \= [] -> write('__'), twb_write_terms(Terms,'__') ; true).
twb_write(P & Q) :-
    write('('),
    twb_write(P),
    write(' & '),
    twb_write(Q),
    write(')').
twb_write(P | Q) :-
    write('('),
    twb_write(P),
    write(' v '),
    twb_write(Q),
    write(')').
twb_write(P => Q) :-
    write('('),
    twb_write(P),
    write(' -> '),
    twb_write(Q),
    write(')').
twb_write(P <=> Q) :-
    write('('),
    twb_write(P),
    write(' <-> '),
    twb_write(Q),
    write(')').
twb_write(~P) :-
    write('~ ('),
    twb_write(P),
    write(')').
twb_write(!([]:P)) :-
    twb_write(P).
twb_write(!([V:T|Vs]:P)) :-
    bagof(Pb,(Val^(call(T,Val),subs(V,Val,!(Vs:P),Pb))),Pbs),
    joinlist('&',Pbs,Enumed),
    twb_write(Enumed).
twb_write(?([]:P)) :-
    twb_write(P).
twb_write(?([V:T|Vs]:P)) :-
    bagof(Pb,(Val^(call(T,Val),subs(V,Val,!(Vs:P),Pb))),Pbs),
    joinlist('|',Pbs,Enumed),
    twb_write(Enumed).
twb_write(knows(A,P)) :-
    write('(['),
    twb_write_path(A),
    write('] ('),
    twb_write(P),
    write('))').
twb_write(pknows(E,P)) :-
    write('(['),
    twb_write_path(E),
    write('] ('),
    twb_write(P),
    write('))').

twb_write_terms([],_).
twb_write_terms([T],_) :-
    twb_write_term(T), !.
twb_write_terms([T,T2|Ts],Sep) :-
    twb_write_term(T),
    write(Sep),
    twb_write_terms([T2|Ts],Sep).

twb_write_term(T) :-
    T =.. [F|Args],
    ( length(Args,0) ->
      write(F)
    ;
      write(F), write('_'),
      twb_write_terms(Args,'_')
    ).
    

twb_write_axioms([]) :-
    write('Verum').
twb_write_axioms([A|Axs]) :-
    twb_write(A), write(' & '),
    twb_write_axioms(Axs).


twb_write_path(E1 ; E2) :-
    write('('),
    twb_write_path(E1),
    write(' ; '),
    twb_write_path(E2),
    write(')').
twb_write_path(E1 | E2) :-
    write('('),
    twb_write_path(E1),
    write(' U '),
    twb_write_path(E2),
    write(')').
twb_write_path(?(P)) :-
    write('( ? '),
    twb_write(P),
    write(' )').
twb_write_path(E*) :-
    write('( * '),
    twb_write_path(E),
    write(' )').
twb_write_path(A) :-
    write(A).

