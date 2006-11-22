proc {ParallelDo D Exec}
    PSearch={New Search.parallel
        init(agent1:1#ssh agent2:1#ssh)}
  in
    Exec={PSearch one(Goloz $)}
end 
