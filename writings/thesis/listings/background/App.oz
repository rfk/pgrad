
functor

import

  Application
  System
  Reverse
  Member
  Search

define

  L = [1 2 3 4 5]
  
  R = {Reverse.reverse L $}
  {System.show reverse(L R)}
  FirstMem = {Search.base.one proc {$ E} {Member.member E L} end }
  {System.show first(L FirstMem)}
  AllMem = {Search.base.all proc {$ E} {Member.member E L} end }
  {System.show all(L AllMem)}
  {Application.exit 0}

end

