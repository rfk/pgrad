proc {TransStar D S Dp Sp}
  choice  Dp=D Sp=S
  []  Dr Sr in {Trans D S Dr Sr}
               {TransStar Dr Sr Dp Sp}
  end
end

proc {Do D S Sp}
  local Dp in
    {TransStar D S Dp Sp}
    {Final Dp Sp}
  end
end

TODO: test this procedure
proc {EvalOffline D Exec}
  Exec={Search.base.one proc {$ E} {Do D s0 E} end}
end 
