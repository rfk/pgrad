%
%  QuantSet.oz:  implements a set of quantified subformulae
%
%  This data structure holds the quantified subformulae encountered
%  along a path, both universally quantified (traversed via positive edge)
%  and existentially quantified (traversed via negative edge).
%
%  Each subformula is stored along with the current variable binding stack
%  at the time it is encountered.  When a path is extended by a subformula,
%  this binding needs to become the active binding.
%
%  Functions are:
%
%    PushA:  Add a universally-quantified formula + binding
%    PushE:  Add an existentially-quantified formula + binding
%    PopE:   Utilise an E-formula. They can only be used once
%    InstA:  Instantiate an A-formula. They can be used many times
%
%  A variety of constraints are posted internally to ensure, for example,
%  that the same A-formula is not instantiated with the same term more than
%  once (redundant) and is not instantiated again before its previous
%  instantiation has been bound (again, redundant).
%

functor

export

  Init
  PushA
  PushE
  PopE
  InstA

  Test

define

  proc {Init QS}
    % The E formulae are simply stored on a list, since they can only
    % be used once.  The A formulae are stored on a queue so they are
    % selected fairly (round robin).
    QS = qs( e: nil
             a: a(head:nil tail:nil))
  end

  proc {PushA QSIn Q B QSOut}
    AIn = QSIn.a AOut
  in
    AOut = {Record.adjoinAt AIn tail (Q#B#nil)|AIn.tail}
    QSOut = {Record.adjoinAt QSIn a AOut}
  end

  proc {PushE QSIn Q B QSOut}
    EIn = QSIn.e EOut
  in
    EOut = (Q#B)|EIn
    QSOut = {Record.adjoinAt QSIn e EOut}
  end

  proc {PopE QSIn Q B QSOut}
    case QSIn.e of QH|QHs then BOld Nm V in
        (Q#BOld) = QH
        QSOut = {Record.adjoinAt QSIn e QHs}
        % We're relying on the receiving code to give the variable a new name
        B = v_e(Nm V)|BOld
        % To maintain soundness, none of the free variables that quantify
        % over this formula can be allowed to unify with V.
        for Vf in BOld do
          if {IsFree Vf} then
              not Vf = v_e(Nm V) end
          end
        end
    else 
        QSOut=QSIn Q=nil B=nil
    end
  end

  %
  %  Make a fresh instance of a universally quantified subformula.
  %
  proc {InstA QSIn Q B QSOut}
    {InstA_acc QSIn Q B nil QSOut}
  end

  proc {InstA_acc QSIn Q B NoGood QSOut}
    QST QT BT IT VNew Found
  in
    QST = {TakeA QSIn (QT#BT#IT)}
    % Nothing left in the list, can't instantiate
    if QT == nil then Q=nil B=nil QSOut = {GiveA QSIn NoGood}
    else
      % Ensure that the previous instantiation has been bound to something.
      % If not, add it to the NoGood list and try again.
      if IT \= nil then
        if {IsFree IT.1} then
          Found = false
          QSOut = {InstA_acc QST Q B (QT#BT#IT)|NoGood}
        else Found = true end
      else Found = true end
      if Found then
         Q = QT
         B = VNew|BT
         QSOut = {GiveA QST (QT#BT#(VNew|IT))|NoGood}
         % Assert that a binding is never repeated.
         % This would be redundant for the proof search.
         for VOld in IT do
           not VOld = VNew end
         end
      end
    end
  end

  proc {TakeA QSIn (Q#B#I) QSOut}
    AOut
  in
    case QSIn.a.head of QH|QHs then
        (Q#B#I) = QH
        AOut = {Record.adjoinAt QSIn.a head QHs}
        QSOut = {Record.adjoinAt QSIn a AOut}
    else
        if QSIn.a.tail == nil then QSIn=QSOut (Q#B#I)=(nil#nil#nil)
        else
          R = {List.reverse QSIn.a.tail} Qs in
          (Q#B#I)|Qs = R
          AOut = {Record.adjoinList QSIn.a [head#Qs tail#nil]}
          QSOut = {Record.adjoinAt QSIn a AOut}
        end
    end
  end

  proc {GiveA QSIn AL QSOut}
    case AL of A|As then AOut QSOutT in
        AOut = {Record.adjoinAt QSIn.a tail A|QSIn.a.tail} 
        QSOutT = {Record.adjoinAt QSIn a AOut}
        QSOut = {GiveA QSOutT As}
    else QSOut = QSIn end
  end


  proc {Test}
    S = {Init}
    S1 S2 S3 S4
    Q1 Q2
    B1 B2
    V1
  in
    S1 = {PushA S 1 [a]}
    S1.e = nil
    S1.a.head = nil
    S1.a.tail = [1#[a]#nil]
    S2 = {PushA S1 2 [b c]}
    S2.a.head = nil
    S2.a.tail = [2#[b c]#nil 1#[a]#nil]
    S3 = {InstA S2 Q1 B1}
    S3.a.head = [2#[b c]#nil]
    S3.a.tail = [1#[a]#[V1]]
    Q1 = 1
    B1 = [_ a] {IsFree B1.1 true}
    {IsFree V1 true}
    B1.1 == V1 = true
    S4 = {InstA S3 Q2 B2}
    S4.a.tail = [2#[b c]#_ 1#[a]#_]
    S4.a.head = nil
    Q2 = 2
    B2 = [_ b c] {IsFree B2.1 true}
    _ = {InstA S4 nil nil}
  end

end

