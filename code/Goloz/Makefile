

FUNCTORS = LP.ozf Time.ozf Sitcalc.ozf Domain.ozf Agent.ozf MIndiGolog.ozf Memo.ozf FOF/ListDict.ozf FOF/OpenMap.ozf FOF/BDD.ozf FOF/FOF.ozf FOF/TermSet.ozf FOF/QuantSet.ozf FOF/EQSet.ozf

%.ozf: %.oz
	ozc -c $< -o $@

%.exe: %.oz
	ozc -x $< -o $@

goloz: Goloz.oz $(FUNCTORS)
	ozc -x $< -o goloz 

test: RunTests.exe $(FUNCTORS)
	./RunTests.exe

clean:
	rm -rf *.ozf *.exe goloz

todo:
	grep 'TODO' *.*

