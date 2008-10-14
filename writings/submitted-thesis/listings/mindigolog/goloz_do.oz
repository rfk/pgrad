proc {TransStar D S Dp Sp}
  choice  Dp=D Sp=S
  []  Dr Sr in {Trans D S Dr Sr} {TransStar Dr Sr Dp Sp}
  end
end

proc {Do D S Sp}
   Dp in
   {TransStar D S Dp Sp}
   {Final Dp Sp}
end
