
functor

import

  Open
  Application
  Property

  LP at 'Utils/LP.ozf'
  Set at 'Utils/Set.ozf'

  OpenMap at 'Utils/OpenMap.ozf'
  ListDict at 'Utils/ListDict.ozf'
  Memo at 'Utils/Memo.ozf'
  IntMap at 'Utils/IntMap.ozf'

  VarMap at 'FOF/VarMap.ozf'
  TermSet at 'FOF/TermSet.ozf'
  QuantSet at 'FOF/QuantSet.ozf'
  EQSet at 'FOF/EQSet.ozf'
  BDD at 'FOF/BDD.ozf'
  FOF at 'FOF/FOF.ozf'

define

  {Property.put 'print.width' 1000}
  {Property.put 'print.depth' 1000}
  {Property.put 'errors.width' 1000}
  {Property.put 'errors.depth' 1000}

  StdOut = {New Open.file init(name: stdout flags: [write])}
  proc {Print S}
    {StdOut write(vs: S#"\n")}
  end

  {Print "\n\n====  Running Tests  ===\n"}  

  {Print "\n==  Testing LP\n"}
  {LP.test}
  {Print passed}

  {Print "\n==  Testing Set\n"}
  {Set.test}
  {Print passed}

  {Print "\n==  Testing OpenMap\n"}
  {OpenMap.test}
  {Print passed}

  {Print "\n==  Testing IntMap\n"}
  {IntMap.test}
  {Print passed}

  {Print "\n==  Testing ListDict\n"}
  {ListDict.test}
  {Print passed}

  {Print "\n==  Testing Memo\n"}
  {Memo.test}
  {Print passed}

  {Print "\n==  Testing VarMap\n"}
  {VarMap.test}
  {Print passed}

  {Print "\n==  Testing TermSet\n"}
  {TermSet.test}
  {Print passed}

  {Print "\n==  Testing QuantSet\n"}
  {QuantSet.test}
  {Print passed}

  {Print "\n==  Testing EQSet\n"}
  {EQSet.test}
  {Print passed}

  {Print "\n==  Testing BDD\n"}
  {BDD.test}
  {Print passed}

  {Print "\n==  Testing FOF\n"}
  {FOF.test}
  {Print passed}

  {Print "\n\n===  Done  ===\n\n"}
  {Application.exit 0}

end
