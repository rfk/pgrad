functor

import

  JointExec at 'SitCalc/JointExec.ozf'
  Planner at '/storage/uni/pgrad/code/Goloz/SitCalc/Planner.ozf'

  Browser
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

  functor SearchFunc
  import
    Planner at '/storage/uni/pgrad/code/Goloz/SitCalc/Planner.ozf'
  export
    Script
  define
    proc {Script JE}
      {Planner.plan pcall(makeSalad(bowl(1))) JE}
    end
  end

  {Browser.browse Plan}
  Searcher = {New Search.parallel init(grapefruit:1#ssh)}
  {Searcher trace(true)}
  Plan = {Searcher one(SearchFunc $)}
  if Plan \= nil then
    {JointExec.writeDotFile Plan.1
       {New Open.file init(name: 'plan.dot' flags:[write create truncate])}}
    {JointExec.writeDotFileAgt Plan.1 thomas
       {New Open.file init(name: 'plan_t.dot' flags:[write create truncate])}}
  end
  {Application.exit 0}

end
