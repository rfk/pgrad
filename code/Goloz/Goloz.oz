functor

import

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

  functor SearchFunc
  import
    Planner at '/storage/uni/pgrad/code/Goloz/SitCalc/Planner.ozf'
  export
    Script
  define
    proc {Script JE}
      {Planner.plan pcall(chopTypeInto(lettuce bowl(1))) JE}
    end
  end

  Searcher = {New Search.parallel init(grapefruit:1#ssh mango:1#ssh)}
  {Searcher trace(true)}
  {Browser.browse Plan}
  Plan = {Searcher one(SearchFunc $)}
  if Plan \= nil then
    {JointExec.writeDotFile Plan
       {New Open.file init(name: 'plan.dot' flags:[write create truncate])}}
    {JointExec.writeDotFileAgt Plan thomas
       {New Open.file init(name: 'plan_t.dot' flags:[write create truncate])}}
  end
  %{Application.exit 0}

end
