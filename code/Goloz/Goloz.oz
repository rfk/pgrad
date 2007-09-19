functor

import

  SitCalc at 'SitCalc/SitCalc.ozf'
  MIndiGolog

  Browser
  Search
  Explorer

define

  local JP Dp Ep Q in
    proc {Q A}
      Dp#Ep = A in
      {MIndiGolog.trans test(impl(p(a) p(_))) now Dp Ep}
    end
    %{Explorer.object script(Q)}
    {Browser.browse {Search.base.all Q}}
    %{MIndiGolog.jointPlan pcall(main) JP}
    %{SitCalc.jplan.print JP}  
  end

end
