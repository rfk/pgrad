%
%  SimpleFOF.oz - simple first-order theorem prover.
%
%  Heh, not really, we are basically a propositional prover.
%  But the proper prover isn't working yet.  Anyway, whatever...
%

functor

export

  Lang
  TransformFunc
  Tautology
  Contradiction
  Simplify

define

  Lang = _

  proc {TransformFunc Transformer Func}
    fun {Func F}
      case F of true then true
      []   false then false
      []   all(X F1) then all(X {Func F1 A})
      []   exists(X F1) then exists(X {Func F1 A})
      []   and(F1 F2) then and({Func F1 A} {Func F2 A})
      []   'or'(F1 F2) then 'or'({Func F1 A} {Func F2 A})
      []   neg(F1) then neg({Func F1 A})
      []   impl(F1 F2) then impl({Func F1 A} {Func F2 A})
      []   equiv(F1 F2) then and({Func F1 A} {Func F2 A})
      []   ite(C F1 F2) then ite({Func C A} {Func F1 A} {Func F2 A})
      else {Tranformer F}  end
    end
  end

  

end

