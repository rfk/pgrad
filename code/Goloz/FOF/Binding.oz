%
%  Binding.oz:  routines for managing a stack of variable bindings.
%
%  This module manages a stack of variable bindings over de Bruijn indices.
%  Values pushed onto the stack are simply terms.  When applied to a record
%  with {bind}, terms of the form v_b(N) are replaced by the appropriate
%  entry from the stack.  Conversely, {unbind} will replace names from
%  the stack with the appropriate variable term.

functor

import

  LP at '../LP.ozf'

export

  Init
  Push
  Pop
  Bind
  Unbind

define

  proc {Init S}
    S=nil
  end

  proc {Push SIn Nm SOut}
    SOut = Nm|SIn
  end

  proc {Pop SIn V SOut}
    SIn = V|SOut
  end

  proc {GetVar S Nm Var}
    {GetVarRec S 0 Nm Var}
  end
  proc {GetVarRec S I Nm Var}
    case S of nil then Var = nil
    else N2|S2 = S in
        if {LP.termEq Nm N2} then Var = I
        else {GetVarRec S2 I+1 Nm Var} end
    end
  end

  proc {GetName S Var Nm}
    {GetNameRec S 0 Var Nm}
  end
  proc {GetNameRec S I Var Nm}
    case S of nil then Nm = v_b(Var)
    else N2|S2=S in
        if Var == I then Nm = N2
        else {GetNameRec S2 I+1 Var Nm} end
    end
  end
 
  proc {Bind S RIn ROut}
    case RIn of v_b(Var) then ROut = {GetName S Var}
    else ROut = {Record.map RIn fun {$ I} {Bind S I} end}
    end
  end

  proc {Unbind S RIn ROut}
    Var = {GetVar S RIn}
  in
    if Var == nil then ROut = {Record.map RIn fun {$ I} {Unbind S I} end}
    else ROut = v_b(Var) end
  end

end
