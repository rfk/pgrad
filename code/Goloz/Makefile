

FUNCTORS = ListDict.ozf OpenMap.ozf LP.ozf BDD.ozf FOF.ozf Time.ozf Sitcalc.ozf Domain.ozf Agent.ozf MIndiGolog.ozf

%.ozf: %.oz
	ozc -c $< -o $@

%.oza: %.oz
	ozc -c $< -o $@

%.exe: %.oz
	ozc -x $< -o $@

goloz: Goloz.oz $(FUNCTORS)
	ozc -x $< -o goloz 

clean:
	rm -rf *.ozf *.oza goloz

