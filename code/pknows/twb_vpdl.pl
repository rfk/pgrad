%
%  twb_vpdl.pl:  interface to our VPDL prover built using Tableaux Workbench
%
%  The main predicate we export is entails/2, which shells out to a stand-alone
%  prover for "PDL-plus-variable-assignment".
%
%  The Tableaux Workbench suite can be obtained from:
%     
%        http://twb.rsise.anu.edu.au/
%
%  Then use `cd vpdl && twbcompile vpdl.ml` to build the prover.
%

twb_pdl_exe('vpdl/vpdl.twb').

entails(Axs,Conc) :-
    maplist(copy_term,Axs,Axs2),
    copy_term(Conc,Conc2),
    twb_pdl_prove(Axs2,Conc2,yes).

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
    twb_pdl_exe(CmdFile),
    sformat(PCmd,'~w < ~w > ~w',[CmdFile,InFile,OutFile]),
    shell(PCmd,_),
    % Grep output file for "Result:Closed" indicating truthity
    sformat(TCmd,'grep "Result:Closed" ~w > /dev/null',[OutFile]),
    ( shell(TCmd,0) ->
        Result = yes
    ;
        % Propositional prover, so we cannot get Result=unknown
        Result = no
    ).


%
%  twb_write(P)  -  write formula in TWB PDL format
%

twb_write(P) :-
    twb_write_fml(P), !.

twb_write_fml(true) :-
    write(' (Verum) '), !.
twb_write_fml(false) :-
    write(' (Falsum) '), !.
twb_write_fml(A=B) :-
    write('( '),
    twb_write_term(A),
    write(' == '),
    twb_write_term(B),
    write(' )').
twb_write_fml(A\=B) :-
    write('~ ( '),
    twb_write_term(A),
    write(' == '),
    twb_write_term(B),
    write(' )').
twb_write_fml(P) :-
    is_atom(P),
    twb_write_pred(P).
twb_write_fml(P & Q) :-
    write('('),
    twb_write_fml(P),
    write(' & '),
    twb_write_fml(Q),
    write(')').
twb_write_fml(P | Q) :-
    write('('),
    twb_write_fml(P),
    write(' v '),
    twb_write_fml(Q),
    write(')').
twb_write_fml(P => Q) :-
    write('('),
    twb_write_fml(P),
    write(' -> '),
    twb_write_fml(Q),
    write(')').
twb_write_fml(P <=> Q) :-
    write('('),
    twb_write_fml(P),
    write(' <-> '),
    twb_write_fml(Q),
    write(')').
twb_write_fml(~P) :-
    write('~ ('),
    twb_write_fml(P),
    write(')').
twb_write_fml(!([]:P)) :-
    twb_write_fml(P).
twb_write_fml(!([V:T|Vs]:P)) :-
    bagof(Pb,(Val^(call(T,Val),subs(V,Val,!(Vs:P),Pb))),Pbs1),
    maplist(copy_fml,Pbs1,Pbs),
    joinlist('&',Pbs,Enumed1),
    simplify(Enumed1,Enumed),
    twb_write_fml(Enumed).
twb_write_fml(?([]:P)) :-
    twb_write_fml(P).
twb_write_fml(?([V:T|Vs]:P)) :-
    bagof(Pb,(Val^(call(T,Val),subs(V,Val,!(Vs:P),Pb))),Pbs1),
    maplist(copy_fml,Pbs1,Pbs),
    joinlist('|',Pbs,Enumed1),
    simplify(Enumed1,Enumed),
    twb_write_fml(Enumed).
twb_write_fml(knows(A,P)) :-
    write('( ['),
    write(A),
    write('] ('),
    twb_write_fml(P),
    write('))').
twb_write_fml(pknows0(E,P)) :-
    epath_vars(E,Vars),
    epath_enum_vars(E,En1),
    epath_elim_impossible_branches(En1,[],En),
    ( En = (?false) ->
        write(' (Verum) ')
    ; En = (?true) ->
        twb_write_fml(P)
    ;
        write('( ['),
        number_vars(Vars),
        twb_write_path(En),
        write('] ('),
        twb_write_fml(P),
        write('))')
    ).

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
    
twb_write_pred(P) :-
    P =.. [F|Terms],
    write(F),
    (Terms \= [] -> write('__'), twb_write_terms(Terms,'__') ; true).

twb_write_axioms([]) :-
    write('Verum').
twb_write_axioms([A]) :-
    twb_write_fml(A).
twb_write_axioms([A|Axs]) :-
    twb_write_fml(A), write(' & '),
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
    twb_write_fml(P),
    write(' )').
twb_write_path(E*) :-
    write('( * '),
    twb_write_path(E),
    write(' )').
twb_write_path(-VA) :-
    ( VA = [] ->
      twb_write_path(?true)
    ;
      write('( '),
      twb_write_vassign(VA),
      write(' )')
    ).
twb_write_path(A) :-
    write(A).

twb_write_vassign([]).
twb_write_vassign([(X:V)|Xs]) :-
    write('! '), write(X), write(' <= '), twb_write_term(V), write(' '),
    twb_write_vassign(Xs).

