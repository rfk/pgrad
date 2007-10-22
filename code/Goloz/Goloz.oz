functor

import

  JointExec at 'SitCalc/JointExec.ozf'
  Planner at '/storage/uni/pgrad/code/Goloz/SitCalc/Planner.ozf'

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
      {Planner.plan pcall(makeSalad(bowl(1))) JE}
    end
  end

%  Searcher = {New Search.parallel init(mango:1#ssh)}
%  {Searcher trace(true)}
%  Plan = {Searcher one(SearchFunc $)}
  Plan = {Search.base.one proc {$ JE} {Planner.plan pcall(makeSalad(bowl(1))) JE} end}
  if Plan \= nil then
    {JointExec.writeDotFile Plan.1
       {New Open.file init(name: 'plan.dot' flags:[write create truncate])}}
    {JointExec.writeDotFileAgt Plan.1 thomas
       {New Open.file init(name: 'plan_t.dot' flags:[write create truncate])}}
  end
  {Application.exit 0}

end
