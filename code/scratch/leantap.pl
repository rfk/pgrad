%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% $Id: leantap.pl,v 2.3 1994/12/14 18:09:13 posegga Exp $
% Sicstus Prolog
% Copyright (C) 1993: Bernhard Beckert & Joachim Posegga
%                     Universit"at Karlsruhe
%                     Email: {beckert|posegga}@ira.uka.de
%
% Purpose:            \LeanTaP: tableau-based theorem prover for NNF.
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

:- module(leantap,[prove/2,prove_uv/2]).

:- 	use_module(library(lists),[append/3]).
:-	use_module(unify,[unify/2]).

%%%%%%%%%% BEGIN OF TOPLEVEL PREDICATES
	
% -----------------------------------------------------------------
% prove(+Fml,?VarLim)
% prove_uv(+Fml,?VarLim)
%
% succeeds if there is a closed tableau for Fml with not more
% than VarLim free variables on each branch.
% prove_uv uses universal variables, prove does not.
%
% Iterative deepening is used when VarLim is unbound.
% Examples: 
%
% | ?- prove((p(a) , -p(f(f(a))) , all(X,(-p(X) ; p(f(X))))), 1).
% no
% | ?- prove((p(a) , -p(f(f(a))) , all(X,(-p(X) ; p(f(X))))), 2).
% yes
%

prove(Fml,VarLim) :- nonvar(VarLim),!,prove(Fml,[],[],[],VarLim).
prove(Fml,Result) :-
	iterate(VarLim,1,prove(Fml,[],[],[],VarLim),Result).

prove_uv(Fml,VarLim) :- nonvar(VarLim),!,prove(Fml,[],[],[],[],[],VarLim).

prove_uv(Fml,Result) :-
	iterate(VarLim,1,prove(Fml,[],[],[],[],[],VarLim),Result).


iterate(Current,Current,Goal,Current) :- nl,
	write('Limit = '),
	write(Current),nl,
	Goal.

iterate(VarLim,Current,Goal,Result) :-
	Current1 is Current + 1,
	iterate(VarLim,Current1,Goal,Result).

%%%%%%%%%% END OF TOPLEVEL PREDICATES


% -----------------------------------------------------------------
% prove(+Fml,+UnExp,+Lits,+FreeV,+VarLim)
%
% succeeds if there is a closed tableau for Fml with not more
% than VarLim free variables on each branch.
%  Fml: inconsistent formula in skolemized negation normal form.
%       syntax: negation: '-', disj: ';', conj: ','
%       quantifiers: 'all(X,<Formula>)', where 'X' is a prolog variable.
%
%  UnExp:    list of formula not yet expanded
%  Lits:     list of literals on the current branch
%  FreeV:    list of free variables on the current branch
%  VarLim:   max. number of free variables on each branch
%            (controlls when backtracking starts and alternate
%            substitutions for closing branches are considered)
%

prove((A,B),UnExp,Lits,FreeV,VarLim) :- !,
	prove(A,[B|UnExp],Lits,FreeV,VarLim).

prove((A;B),UnExp,Lits,FreeV,VarLim) :- !,
	prove(A,UnExp,Lits,FreeV,VarLim),
	prove(B,UnExp,Lits,FreeV,VarLim).
        
prove(all(X,Fml),UnExp,Lits,FreeV,VarLim) :- !,
	\+ length(FreeV,VarLim),
	copy_term((X,Fml,FreeV),(X1,Fml1,FreeV)),
	append(UnExp,[all(X,Fml)],UnExp1),
	prove(Fml1,UnExp1,Lits,[X1|FreeV],VarLim).

prove(Lit,_,[L|Lits],_,_) :-
	(Lit = -Neg; -Lit = Neg) ->
	(unify(Neg,L); prove(Lit,[],Lits,_,_)).

prove(Lit,[Next|UnExp],Lits,FreeV,VarLim) :-
	prove(Next,UnExp,[Lit|Lits],FreeV,VarLim).

% -----------------------------------------------------------------
% prove(+Fml,+UnExp,+Lits,+DisV,+FreeV,+UnivV,+VarLim)
%
% same as prove/5 above, but uses universal variables.
% additional parameters:
% DisV:   list of non-universal variables on branch
% UnivV:  list of universal variables on branch

prove((A,B),UnExp,Lits,DisV,FreeV,UnivV,VarLim) :- !,
	prove(A,[(UnivV:B)|UnExp],Lits,DisV,FreeV,UnivV,VarLim).

prove((A;B),UnExp,Lits,DisV,FreeV,UnivV,VarLim) :- !,
	copy_term((Lits,DisV),(Lits1,DisV)),
	prove(A,UnExp,Lits,(DisV+UnivV),FreeV,[],VarLim),
	prove(B,UnExp,Lits1,(DisV+UnivV),FreeV,[],VarLim).

prove(all(X,Fml),UnExp,Lits,DisV,FreeV,UnivV,VarLim) :- !,
	\+ length(FreeV,VarLim),
	copy_term((X,Fml,FreeV),(X1,Fml1,FreeV)),
	append(UnExp,[(UnivV:all(X,Fml))],UnExp1),
	prove(Fml1,UnExp1,Lits,DisV,[X1|FreeV],[X1|UnivV],VarLim).

prove(Lit,_,[L|Lits],_,_,_,_) :-
	(Lit = -Neg; -Lit = Neg ) ->
	(unify(Neg,L); prove(Lit,[],Lits,_,_,_,_)).

prove(Lit,[(UnivV:Next)|UnExp],Lits,DisV,FreeV,_,VarLim) :-
	prove(Next,UnExp,[Lit|Lits],DisV,FreeV,UnivV,VarLim).
