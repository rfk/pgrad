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
      {MIndiGolog.plan pick(obj seq(seq(acquire(thomas board(2)) acquire(thomas knife(1))) test(has_object(thomas obj)))) now A}
    end
    %{Explorer.object script(Q)}
    {Browser.browse {Search.base.all Q}}
    %{MIndiGolog.jointPlan pcall(main) JP}
    %{SitCalc.jplan.print JP}  
  end

end
