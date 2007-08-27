%
%  QuantSet.oz:  implements a set of quantified subformulae
%

functor

export

  Init
  Put
  Pop
  Inst

  Test

define

  proc {Init QS}
    QS = unit(head: nil tail: nil)
  end

  proc {Put Q B QSin QSout}
    QSout = {Record.adjoinAt QSin tail (Q#B)|QSin.tail}
  end

  proc {Pop Q B QSIn QSOut}
    case QSIn.head of QH|QHs then
        (Q#B) = QH
        QSOut = {Record.adjoinAt QSIn head QHs}
    else 
        if QSIn.tail == nil then QSIn=QSOut Q=nil B=nil
        else
          (Q#B)|Qs = {List.reverse QSIn.tail} in
          QSOut = {Record.adjoinList QSIn [head#Qs tail#nil]}
        end
    end
  end

  proc {Inst Q B QSIn QSOut}
    case QSIn.head of QH|QHs then
        (Q#B) = QH
        QSOut = {Record.adjoinList QSIn [head#QHs tail#(QH|QSIn.tail)]}
    else
        if QSIn.tail == nil then QSIn=QSOut Q=nil B=nil
        else
          (Q#B)|Qs = {List.reverse QSIn.tail} in
          QSOut = {Record.adjoinList QSIn [head#Qs tail#nil]}
        end
    end
  end


  proc {Test}
    skip
  end

end

