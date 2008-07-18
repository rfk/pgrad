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
    % We need to include object equality axioms for each object.
    write('('),
    twb_write_axioms(Axioms), !,
    write(' & '),
    twb_write_equality_axioms,
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
        Result = no
    % Propositional prover, so we cannot get Result=unknown
    ).


%
%  twb_write(P)  -  write formula in TWB PDL format
%
twb_write(A=B) :-
    ground(A), ground(B),
    ( A == B ->
        write('Verum')
    ; ( twb_is_var(A) ; twb_is_var(B) ) ->
        twb_write(equals(A,B))
    ;
        write('Falsum')
    ), !.
twb_write(A\=B) :-
    ground(A), ground(B),
    ( A == B ->
        write('Falsum')
    ; ( twb_is_var(A) ; twb_is_var(B) ) ->
        twb_write( ~ equals(A,B))
    ;
        write('Verum')
    ), !.
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
    write('( ['),
    write(A),
    write('] ('),
    twb_write(P),
    write('))').
twb_write(pknows0(E,P)) :-
    write('( ['),
    epath_vars(E,Vars),
    number_vars(Vars),
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


twb_write_equality_axioms :-
    setof(Ax,O^(object(O),Ax=equals(O,O)),Axs1),
    maplist(make_cknows_fml,Axs1,Axs),
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
twb_write_path(!(X:T)) :-
    bagof(V,call(T,V),Vs),
    write('( '),
    twb_write_vassigns(Vs,X),
    write(' )').
twb_write_path(A) :-
    write(A).

twb_write_vassigns([],_) :-
    write('( ? Falsum )').
twb_write_vassigns([V|Vs],X) :-
    write('( ! '), write(X), write(' <= '), twb_write_term(V), write(' )'),
    write(' U '), twb_write_vassigns(Vs,X).

twb_is_var(V) :-
    atom(V),
    name(x,[X]),
    atom_codes(V,[X|_]).

