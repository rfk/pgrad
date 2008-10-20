functor

import

  JointExec
  Planner

  Search
  Property
  Open
  Application
  System

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  Plan = {Search.base.one proc {$ JE}
           {Planner.plan pcall(main) JE}
         end}
  if Plan \= nil then
    {JointExec.writeDotFile Plan.1
       {New Open.file init(name: 'plan.dot' flags:[write create truncate])}}
  end
  {System.show Plan}

  {Application.exit 0}

end
