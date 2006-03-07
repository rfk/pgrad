%% Version: 1.01p  -  Date: 04/01/2002  -  File: nnf_mm.pl
%%
%% Purpose: - computes Skolemized negation normal form for a
%%            first-order formula (based on leanTAP's nnf.pl)
%%          - computes disjunctive normal form for a formula
%%            in Skolemized negational normal form
%%          - computes a matrix form (and applies MULT and TAUT
%%            reductions) for a formula in disjunctive normal form
%%              
%% Author:  Jens Otten (jens@leancop.de)
%%
%% Usage:   make_matrix(Fml,M)  % where F is a first-order formula
%%                              % and M its matrix (clausal) form
%%
%% Example: make_matrix(ex Y: (all X: ((f(Y) => f(X))) ),Matrix).
%%          Matrix = [[-(f(X1))], [f(1 ^ [X1])]]
%%
%% Web:     www.leancop.de


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% $Id: nnf.pl,v 2.4 1997/10/30 21:06:17 beckert Exp $
% Sicstus Prolog
% Copyright (C) 1993: Bernhard Beckert & Joachim Posegga
%                     Universit"at Karlsruhe
%                     Email: {beckert|posegga}@ira.uka.de
%
% Purpose:            computes Skolemized negation normal form
%                     for a first-order formula       
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
%
%% modified 1999/11/28 Jens Otten  (syntax of connectives/quantifiers)
%% extended 1999/11/28 Jens Otten  (NNF to DNF to matrix/clausal form)
%% modified 2002/01/04 Jens Otten  (using own skolemization technique)
%
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

%%:-      module(nnf,[nnf/2]).  %% only for Sicstus

:- op(1130, xfy, <=>). % equivalence
:- op(1110, xfy, =>).  % implication
%                      % disjunction (;)
%                      % conjunction (,)
:- op( 500, fy, ~).    % negation
:- op( 500, fy, all).  % universal quantifier
:- op( 500, fy, ex).   % existential quantifier
:- op( 500,xfy, :).

% -----------------------------------------------------------------
%  nnf(+Fml,?NNF)
%
% Fml is a first-order formula and NNF its Skolemized negation 
% normal form (where quantifiers have been removed from NNF).
%
% Syntax of Fml:
%  negation: '~', disj: ';', conj: ',', impl: '=>', eqv: '<=>',
%  quant. 'all X:<Formula>', 'ex X:<Formula>' where 'X' is a
%  prolog variable.
%
% Syntax of NNF: negation: '~', disj: ';', conj: ','.
%
% Example:  nnf(ex Y: (all X: ((f(Y) => f(X))) ),NNF).
%           NNF = ~ f(X1) ; f(1 ^ [X1])

nnf(Fml,NNF) :- nnf(Fml,[],NNF,_,1,_).

% -----------------------------------------------------------------
%  nnf(+Fml,+FreeV,-NNF,-Paths,+I,-I1)
%
% Fml,NNF:    See above.
% FreeV:      List of free variables in Fml.
% Paths:      Number of disjunctive paths in Fml.

nnf(Fml,FreeV,NNF,Paths,I,I1) :- 
	(Fml = ~(~A)      -> Fml1 = A;
	 Fml = ~(all X:F) -> Fml1 = (ex X: ~F);
	 Fml = ~(ex X:F)  -> Fml1 = (all X: ~F);
	 Fml = ~((A ; B)) -> Fml1 = ((~A , ~B));
	 Fml = ~((A , B)) -> Fml1 = (~A ; ~B);
	 Fml = (A => B)   -> Fml1 = (~A ; B);
	 Fml = ~((A => B))-> Fml1 = ((A , ~B));
	 Fml = (A <=> B)  -> Fml1 = ((A , B) ; (~A , ~B));
	 Fml = ~((A<=>B)) -> Fml1 = ((A , ~B) ; (~A , B)) ),!,
	nnf(Fml1,FreeV,NNF,Paths,I,I1).

nnf((ex X:F),FreeV,NNF,Paths,I,I1) :- !,  %% positive representation
	copy_term((X,F,FreeV),(X1,F1,FreeV)),  %% uniqe var. names
	nnf(F1,[X1|FreeV],NNF,Paths,I,I1).

nnf((all X:Fml),FreeV,NNF,Paths,I,I1) :- !,  %% positive representation
	copy_term((X,Fml,FreeV),((I^FreeV),Fml1,FreeV)), I2 is I+1,
	nnf(Fml1,FreeV,NNF,Paths,I2,I1).

nnf((A ; B),FreeV,NNF,Paths,I,I1) :- !,  %% positive representation
	nnf(A,FreeV,NNF1,Paths1,I,I2),
	nnf(B,FreeV,NNF2,Paths2,I2,I1),
	Paths is Paths1 * Paths2,
	(Paths1 > Paths2 -> NNF = (NNF2;NNF1);
		            NNF = (NNF1;NNF2)).

nnf((A , B),FreeV,NNF,Paths,I,I1) :- !,  %% positive representation
	nnf(A,FreeV,NNF1,Paths1,I,I2),
	nnf(B,FreeV,NNF2,Paths2,I2,I1),
	Paths is Paths1 + Paths2,
	(Paths1 > Paths2 -> NNF = (NNF2,NNF1);
		            NNF = (NNF1,NNF2)).

nnf(Lit,_,Lit,1,I,I).


%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%
% Copyright (C) 1999: Jens Otten (jens@leancop.de)
%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%%

% -----------------------------------------------------------------
%  make_matrix(+Fml,-Matrix)
%
% Syntax of Fml:
%  negation: '~', disj: ';', conj: ',', impl: '=>', eqv: '<=>',
%  quant. 'all X:<Formula>', 'ex X:<Formula>' where 'X' is a
%  prolog variable.
%
% Syntax of Matrix:
%  Matrix is a list of clauses; a clause is a list of literals.
%
% Example:  make_matrix(ex Y: (all X: ((f(Y) => f(X))) ),Matrix).
%           Matrix = [[-(f(X1))], [f(1 ^ [X1])]]

make_matrix(Fml,Matrix) :-
	nnf(Fml,NNF), dnf(NNF,DNF), mat(DNF,Matrix).

% -----------------------------------------------------------------
%  dnf(+NNF,-DNF)
%
% NNF:    See above.
%
% Syntax of DNF: negation: '~', disj: ';', conj: ',' .
%
% Example:  dnf(((p;~p),(q;~q)),DNF).
%           DNF = (p, q ; p, ~ q) ; ~ p, q ; ~ p, ~ q

dnf(((A;B),C),(F1;F2)) :- !, dnf((A,C),F1), dnf((B,C),F2).
dnf((A,(B;C)),(F1;F2)) :- !, dnf((A,B),F1), dnf((A,C),F2).
dnf((A,B),F) :- !, dnf(A,A1), dnf(B,B1),
	( (A1=(C;D);B1=(C;D)) -> dnf((A1,B1),F) ; F=(A1,B1) ).
dnf((A;B),(A1;B1)) :- !, dnf(A,A1), dnf(B,B1).
dnf(Lit,Lit).

% -----------------------------------------------------------------
%  mat(+DNF,-Matrix)
%
% DNF,Matrix:    See above.
%
% Example:  mat(((p, q ; p, ~ q) ; ~ p, q ; ~ p, ~ q),Matrix).
%           Matrix = [[p, q], [p, -(q)], [-(p), q], [-(p), -(q)]]

mat((A;B),M) :- !, mat(A,MA), mat(B,MB), append(MA,MB,M).
mat((A,B),C) :- !, mat(A,[CA]), mat(B,[CB]), union2(CA,CB,C).
mat(~Lit,[[-Lit]]) :- !.
mat(Lit,[[Lit]]).

% -----------------------------------------------------------------
%  union2/member2  (realizes MULT/TAUT reductions)

union2([],L,[L]).
union2([X|L1],L2,L3) :- member2(X,L2), !, union2(L1,L2,L3).
union2([X|_],L2,[])  :- (-Xn=X;-X=Xn), member2(Xn,L2), !.
union2([X|L1],L2,L3) :- union2(L1,[X|L2],L3).

member2(X,[Y|_]) :- X==Y, !.
member2(X,[_|T]) :- member2(X,T).
