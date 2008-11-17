proc {Step D S Dp Sp}
  choice Sp=res(_ _ S) {Trans D S Dp Sp}
  []     Dr in {Trans D S Dr S} {Step Dr S Dp Sp}
  end
end
