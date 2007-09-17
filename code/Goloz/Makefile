

FUNCTORS = LP.ozf Time.ozf Sitcalc.ozf Domain.ozf Agent.ozf MIndiGolog.ozf \
           PlanFront.ozf Set.ozf DomainBuilder.ozf\
           Mutable/Set.ozf Mutable/Record.ozf Mutable/List.ozf \
           Memo/Memo.ozf Memo/ListDict.ozf Memo/OpenMap.ozf \
           FOF/BDD.ozf FOF/FOF.ozf FOF/TermSet.ozf FOF/QuantSet.ozf \
           FOF/EQSet.ozf FOF/Binding.ozf

%.ozf: %.oz
	ozc -c $< -o $@

%.exe: %.oz
	ozc -x $< -o $@

goloz: Goloz.oz $(FUNCTORS)
	ozc -x $< -o goloz 

test: RunTests.exe $(FUNCTORS)
	./RunTests.exe

clean:
	rm -rf *.ozf *.exe FOF/*.ozf Memo/*.ozf Mutable/*.ozf goloz

todos:
	grep 'TODO' *.* FOF/*.* Memo/*.* Mutable/*/*

