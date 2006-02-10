proc {EvalOfflineDistrib D Exec}
    PS={New Search.parallel
        init(agent1:1#ssh agent2:1#ssh)}
  in
    Exec={PS one(Goloz $)}
end 
