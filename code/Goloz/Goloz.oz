functor

import

  Planner at 'SitCalc/Planner.ozf'
  JointExec at 'SitCalc/JointExec.ozf'

  Browser
  Search
  Property
  Open
  Application

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  proc {Q JE}
      {Planner.plan seq(check_for(thomas lettuce) acquire(thomas lettuce(1))) JE}
  end
  {JointExec.writeDotFile {Search.base.one Q}.1 
               {New Open.file init(name: 'plan.dot' flags:[write create truncate])}}
  {Application.exit 0}

end
