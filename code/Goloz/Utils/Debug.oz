%
%  Debug.oz:  debugging output
%

functor

import

  System

export

  Show
  Print

define

  DoDebug = true

  proc {Show Msg}
    if DoDebug then
      if {VirtualString.is Msg} then
        {System.showInfo Msg}
      else
        {System.show Msg
      end
    end
  end

  proc {Print Msg}
    if DoDebug then
      if {VirtualString.is Msg} then
        {System.printInfo Msg}
      else
        {System.print Msg
      end
    end
  end

end
