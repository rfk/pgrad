proc {Final D S}
  case D of nil then skip
  [] test(Cond) then fail
  [] seq(D1 D2) then {Final D1 S} {Final D2 S}
  [] pick(D1 D2) then choice {Final D1 S}
                      [] {Final D2 S}
                      end
  [] ... <additional cases ommitted> ...
  end
end
