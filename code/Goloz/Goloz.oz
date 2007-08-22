
functor

import

  LP
  Browser
  Search

define

  proc {Proc1 Res}
    choice Res = a
    []     Res = b
    []     Res = c
    end
  end

  proc {Proc2 Res}
    choice Res = d
    []     Res = e
    []     Res = f
    end
  end

  proc {App Res}
    {LP.ifNot Proc1 Proc2 Res}
  end

  {Browser.browse {Search.base.all App}}

end
