proc {ParallelMIndiGolog D S}
    PSearch={New Search.parallel
        init(richard:1#ssh thomas:1#ssh harriet:1#ssh)}
  in
    S={PSearch one(MIndiGolog D $)}
end 
