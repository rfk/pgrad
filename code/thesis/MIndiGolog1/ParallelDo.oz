
functor

import

  LP at '/storage/uni/pgrad/code/thesis/MIndiGolog1/LP.ozf'
  MIndiGolog at '/storage/uni/pgrad/code/thesis/MIndiGolog1/MIndiGolog.ozf'

define

  proc {Script R}
    Dl Sl Spl
  in
    {LP.unserialize Ds Dl}
    {LP.unserialize Ss Sl}
    {MIndiGolog.'do' Dl Sl Spl}
    R = {LP.serialize (Dl#Sl#Spl)}
  end

end
