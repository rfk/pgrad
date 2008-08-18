
functor

import

  Application
  System
  MyList
  Search

define

  L = [1 2 3 4 5]
  
  R = {MyList.reverse L $}
  {System.show reverse(L R)}
  FirstMem = {Search.base.one proc {$ E} {MyList.member E L} end }
  {System.show first(L FirstMem)}
  AllMem = {Search.base.all proc {$ E} {MyList.member E L} end }
  {System.show all(L AllMem)}
  {Application.exit 0}

end

