functor

import

  SitCalc at 'SitCalc/SitCalc.ozf'
  MIndiGolog

  Browser
  Search
  Explorer
  Property
  System

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  local JP Dp Ep Q in
    proc {Q A}
      Dp Ep V in
      %{MIndiGolog.step pcall(chopInto(thomas lettuce(1) bowl(1))) now Dp Ep}
      %{MIndiGolog.step check_for(thomas lettuce) now Dp Ep}
      %{System.printInfo "\n\n  == here == \n\n"}
      {SitCalc.ex.outcomes ex(step(action:[acquire(thomas lettuce(1))] obs:nil) now) A}
      %A = Ep
    end
    {Browser.browse {Search.base.one Q}}
  end

end
