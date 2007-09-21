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
      %{MIndiGolog.steps 2 seq(check_for(thomas lettuce) acquire(thomas lettuce(1))) now Dp Ep}
      {MIndiGolog.jointPlan seq(check_for(thomas lettuce) acquire(thomas lettuce(1))) A}
    end
    {Browser.browse {Search.base.one Q}}
  end

end
