functor

import

  JointExec at 'SitCalc/JointExec.ozf'
  Search
  Open

define

  functor SearchFunc
  import
    Planner at 'SitCalc/Planner.ozf'
  export
    Script
  define
    proc {Script JE}
      {Planner.plan pcall(makeSalad(bowl(1))) JE}
    end
  end

  Searcher = {New Search.parallel init(thomas:1#ssh 
                                       richard:1#ssh
                                       harriet:1#ssh)}
  Plan = {Searcher one(SearchFunc $)}
  if Plan \= nil then
    {JointExec.writeDotFile Plan.1
     {New Open.file init(name:'plan.dot' flags:[write create])}}
  end

end
