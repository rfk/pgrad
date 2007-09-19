functor

import

  SitCalc at 'SitCalc/SitCalc.ozf'
  MIndiGolog

  Browser
  Search
  Explorer
  Property

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  local JP Dp Ep Q in
    proc {Q A}
      Dp#Ep = A V in
      %{MIndiGolog.trans pick(v test(obj_is_type(v board))) now Dp Ep}
      {MIndiGolog.plan pcall(chopInto(thomas lettuce(1) bowl(1))) now Ep}
    end
    %{Explorer.object script(Q)}
    {Browser.browse {Search.base.all Q}}
    %{MIndiGolog.jointPlan pcall(main) JP}
    %{SitCalc.jplan.print JP}  
  end

end
