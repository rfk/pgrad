%
%  LP.oz:  generic logic-programming procedures
%

functor 
import

  Search
  System
  FD

export

  Neg
  Member
  NotMember
  Union
  SubInTerm
  CopyTerm

define

  % Standard negation-as-failure on a nullary procedure
  %
  % Unlike prolog, this cannot close over free variables.  If the
  % input procedure uses free variables, the search will hang waiting
  % for them to be bound.
  %
  proc {Neg P}
    {Search.base.one proc {$ L} {P} L=unit end $} = nil
  end

  % Nondeterministic selection of list member
  %
  proc {Member Elem List}
    choice  List = Elem|_
    []      NewL in List=_|NewL {Member Elem NewL}
    end
  end

  % Assert that element is not a member of the lsit
  %
  proc {NotMember Elem List}
    case List of nil then skip
    []   H|T then not Elem = H end
                  {NotMember Elem T}
    end
  end

  % Set-union of two lists
  %
  proc {Union L1 L2 LF}
    case L1 of
        nil then LF = L2
    []  H|T then local LI in 
          LI = {Union T L2}
          choice {Member H LI} LF = LI
          [] LF = H|LI
          end
        end
    end
  end

  % Term substitution - replace all occurrences of VOld with VNew
  % in TIn, to produce new term TOut.
  %
  proc {SubInTerm VOld VNew TIn TOut}
    if {IsFree TIn} then
      TIn = TOut
    else
      if TIn == VOld then
        TOut = VNew
      else
        if {IsRecord TIn} then
          {SubInTerm_Record VOld VNew TIn TOut}
        else
          TIn = TOut
        end
      end
    end
  end

  proc {SubInTerm_Record VOld VNew RIn ROut}
    Fields = {Arity RIn}
  in
    {Record.clone RIn ROut}
    {ForAll Fields proc {$ F}
                     {SubInTerm VOld VNew RIn.F ROut.F}
                   end}
  end


  proc {CopyTerm TIn TOut}
    if {IsFree TIn} then
      TOut = _
    else
      if {IsDet TIn} then
        if {IsRecord TIn} then
          TOut = {CopyTerm_record TIn}
        else
          % TODO: any other tricky recursive cases?
          TOut = TIn
        end
      else
        if {IsKinded TIn} then Kind in
          {Value.status TIn kinded(Kind)}
          if Kind == int then
              % We assume only linear constraints, so copying min/max is valid
              {FD.decl TOut}
              TOut >=: {FD.reflect.min TIn}
              TOut =<: {FD.reflect.max TIn}
          else
              % TODO: copy other kinded constraints, e.g. records
              TOut = _
          end
        else
          % TODO: any other cases to consider?
          TOut = TIn
        end
      end
    end
  end
    
  proc {CopyTerm_record TIn TOut}
    TOut = {Record.make {Record.label TIn} {Record.arity TIn}}
    {ForAll {Record.arity TIn} proc {$ F}
               {CopyTerm TIn.F TOut.F}
            end}
  end

end

