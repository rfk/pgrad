%
%  VarMap.oz:  mapping from variables to names
%
%  This functor provides a map between variables and names.  It's used
%  to provide stand-ins for variables in places where they cant be used.
%
%  Implementation is as a mutable list of Var#Name pairs.  Names are
%  simply generated with {NewName} in a top-level service (to ensure
%  global uniqueness).
%
%  {Map} takes a record and replaces free variables with terms v_e(Nm) where
%  Nm is the name in the map.  Variables encountered for the first time
%  get a fresh name.  {Unmap} reverses this, replacing v_e(Nm) terms with
%  the corresponding free variables.
%
%  {Bind} takes a record mapping names to values, and binds the corresponding
%  free variables to those values.
%

functor

import

  System
  MList at '../Utils/MList.ozf'
  Service at '../Utils/Service.ozf'

export

  New
  Map
  Unmap
  Bind
  Test
  
define

  S_MakeName = {Service.new proc {$ _ Out} Out={NewName} end}
  proc {MakeName Nm}
    {S_MakeName nil Nm}
  end

  proc {New VM}
    VM = {MList.new}
  end

  proc {Map VM Term Out}
    if {IsFree Term} then Nm in
      Nm = for return:R default:nil V2#N2 in {MList.toList VM} do
             if {System.eq Term V2} then {R N2} end
           end
      if Nm == nil then NmNew in
        NmNew = {MakeName}
        {MList.cons VM Term#NmNew}
        Out = v_e(NmNew)
      else Out = Nm end
    elseif {Not {Record.is Term}} then Out = Term
    else
      Out = {Record.map Term proc {$ I O} {Map VM I O} end}
    end
  end

  proc {Unmap VM Term Out}
    case Term of v_e(Nm) then
      if {IsName Nm} then Var in
        Var = for return:R default:nil V2#N2 in {MList.toList VM} do
                if Term == N2 then {R V2} end
              end
        if {IsFree Var} then Out = Var
        else Out = Term end
      else Out = Term end
    else
      if {Not {Record.is Term}} then
        Out = Term
      else
        Out = {Record.map Term proc {$ I O} {Unmap VM I O} end}
      end
    end
  end

  proc {Bind VM Binding}
    for V#N in {MList.toList VM} do
      V = {Value.condSelect Binding N V}
    end
  end

  proc {Test}
    VM1 N1
  in
    VM1 = {New}
    {Map VM1 p(a _) p(a v_e(N1))}
    {IsName N1 true}
  end

end

