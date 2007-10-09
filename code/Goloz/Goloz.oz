functor

import

  Planner at 'SitCalc/Planner.ozf'

  Browser
  Search
  Property

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  proc {Q JP}
      {Planner.jointPlan seq(check_for(thomas lettuce) acquire(thomas lettuce(1))) JP}
  end
  {Browser.browse {Search.base.one Q}}

end
