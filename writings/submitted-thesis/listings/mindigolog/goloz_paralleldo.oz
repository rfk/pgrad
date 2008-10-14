{IParallelDo D S Sp}
  PDo PSearch Ds Ss Machines
in
  Ds = {LP.serialize D}
  Ss = {LP.serialize S}
  functor PDo
    import
      MG at '/path/to/MIndiGolog.ozf'
      LP at '/path/to/LP.ozf'
    export
      Script
  define
      proc {Script R}
        Dl Sl Spl
      in
        {LP.unserialize Ds Dl}
        {LP.unserialize Ss Sl}
        {MG.'do' Dl Sl Spl}
        R = {LP.serialize (Dl#Sl#Spl)}
      end
  end
  % this constructs a record like: init(jim:1#ssh joe:1#ssh)
  Machines = {Record.make init Control.agents}
  for Agt in {Record.arity Machines} do
    Machines.Agt = 1#ssh
  end
  PSearch = {New Search.parallel Machines}
  [(D#S#Sp)] = {LP.unserialize {PSearch one(PDo $)}}
end
