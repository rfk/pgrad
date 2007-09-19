%
%  VarMap.oz:  mapping from variables to names
%
%  This functor provides a map between variables and names.  It's used
%  to provide stand-ins for variables in places where they cant be used.
%
%  Implementation is as a mutable list of Var#Name pairs.  Names are
%  simply generated with {NewName} in top-level service (to ensure
%  global uniqueness).
%

functor

import

  System
  MList at '../Mutable/List.ozf'

export

  New
  Map
  Unmap
  Bind
  Test
  
define

  local IPort IStream in
    IPort = {Port.new IStream}
    thread
      for _#Out in IStream do
        Out=v_e({NewName})
      end
    end
    proc {MakeName Nm}
      Nm = !!{Port.sendRecv IPort unit}
    end
  end

  proc {New VM}
    VM = {MList.new}
  end

  proc {Map VM Term Out}
    if {IsFree Term} then Nm in
      Nm = for return:R default:nil V2#N2 in {MList.toList VM} do
             if {System.eq Term V2} then {R N2} end
           end
      if Nm == nil then
        Out = {MakeName}
        {MList.cons VM Term#Out}
      else Out = Nm end
    else
      Out = {Record.map Term proc {$ I O} {Map VM I O} end}
    end
  end

  proc {Unmap VM Term Out}
    if {IsName Term} then Var in
      Var = for return:R default:nil V2#N2 in {MList.toList VM} do
             if Term == N2 then {R V2} end
            end
      if {IsFree Var} then Out = Var
      else Out = Term end
    else
      Out = {Record.map Term proc {$ I O} {Unmap VM I O} end}
    end
  end

  proc {Bind VM Binding}
    for V#N in {MList.toList VM} do Name in
      N = v_e(Name)
      V = {Value.condSelect Binding Name V}
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

