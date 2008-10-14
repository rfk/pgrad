proc {Run D S}
  if {IsFinal D S} then
    {Control.log succeeded}
  else Dp Sp C T in
      try {NextStep D S Dp Sp}
          Sp = res(C T S)
          T = {Time.min T}
          {Control.execute C T}
          {Run Dp Sp}
      catch _ then
        {Control.log failed}
      end
  end
end
