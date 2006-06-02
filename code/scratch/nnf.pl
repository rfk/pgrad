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

%:-      module(nnf,[nnf/2]).

:-      op(400,fy,-),    % negation
	op(500,xfy,&),   % conjunction
	op(600,xfy,v),   % disjunction
	op(650,xfy,=>),  % implication
	op(700,xfy,<=>). % equivalence
   
% -----------------------------------------------------------------
%  nnf(+Fml,?NNF)
%
% Fml is a first-order formula and NNF its Skolemized negation 
% normal form.
%
% Syntax of Fml:
%  negation: '-', disj: 'v', conj: '&', impl: '=>', eqv: '<=>',
%  quant. 'all(X,<Formula>)', where 'X' is a prolog variable.
%
% Syntax of NNF: negation: '-', disj: ';', conj: ',', quant.:
%  'all(X,<Formula>)', where 'X' is a prolog variable.
%
% Example:  nnf(ex(Y, all(X, (f(Y) => f(X)))),NNF).
%           NNF =  all(_A,(-(f(all(X,f(ex)=>f(X))));f(_A)))) ?

nnf(Fml,NNF) :- nnf(Fml,[],NNF,_).

% -----------------------------------------------------------------
%  nnf(+Fml,+FreeV,-NNF,-Paths)
%
% Fml,NNF:    See above.
% FreeV:      List of free variables in Fml.
% Paths:      Number of disjunctive paths in Fml.

nnf(Fml,FreeV,NNF,Paths) :- 
	(Fml = -(-A)      -> Fml1 = A;
	 Fml = -all(X,F)  -> Fml1 = ex(X,-F);
	 Fml = -ex(X,F)   -> Fml1 = all(X,-F);
	 Fml = -(A v B)   -> Fml1 = -A & -B;
	 Fml = -(A & B)   -> Fml1 = -A v -B;
	 Fml = (A => B)   -> Fml1 = -A v B;
	 Fml = -(A => B)  -> Fml1 = A & -B;
	 Fml = (A <=> B)  -> Fml1 = (A & B) v (-A & -B);
	 Fml = -(A <=> B) -> Fml1 = (A & -B) v (-A & B)),!,
	nnf(Fml1,FreeV,NNF,Paths).

nnf(all(X,F),FreeV,all(X,NNF),Paths) :- !,
	nnf(F,[X|FreeV],NNF,Paths).

nnf(ex(X,Fml),FreeV,NNF,Paths) :- !,
	copy_term((X,Fml,FreeV),(Fml,Fml1,FreeV)),
	copy_term((X,Fml1,FreeV),(ex,Fml2,FreeV)),
	nnf(Fml2,FreeV,NNF,Paths).

nnf(A & B,FreeV,NNF,Paths) :- !,
	nnf(A,FreeV,NNF1,Paths1),
	nnf(B,FreeV,NNF2,Paths2),
	Paths is Paths1 * Paths2,
	(Paths1 > Paths2 -> NNF = (NNF2,NNF1);
		            NNF = (NNF1,NNF2)).

nnf(A v B,FreeV,NNF,Paths) :- !,
	nnf(A,FreeV,NNF1,Paths1),
	nnf(B,FreeV,NNF2,Paths2),
	Paths is Paths1 + Paths2,
	(Paths1 > Paths2 -> NNF = (NNF2;NNF1);
		            NNF = (NNF1;NNF2)).

nnf(Lit,_,Lit,1).
