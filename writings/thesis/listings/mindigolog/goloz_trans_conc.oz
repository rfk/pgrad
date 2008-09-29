proc {Trans D S Dp Sp}
  [] ...
  []   conc(D1 D2) then choice D1r D2r C1 C2 Cu T in
                                 {Step D1 S D1r res(C1 T S)}
                                 {Step D2 S D2r res(C2 T S)}
                                 {LP.neg proc {$} A in
                                    {LP.member A C1}
                                    {LP.member A C2}
                                    {LP.neg proc {$} {Domain.isExog A} end}
                                 end}
                                 {LP.union C1 C2 Cu}
                                 {Sitcalc.legal Cu T S}
                                 Sp=res(Cu T S) Dp=conc(D1r D2r)
                        []     D1r in {Trans D1 S D1r Sp} Dp=conc(D1r D2)
                        []     D2r in {Trans D2 S D2r Sp} Dp=conc(D1 D2r)
                        end
  [] ...
end
