
functor

import

  Application
  System
  Reverse

define

  L = [1 2 3 4 5]
  
  R = {Reverse.reverse L $}
  {System.show R}
  {Application.exit 0}

end

