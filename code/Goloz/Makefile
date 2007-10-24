

FUNCTORS = Agent.ozf Domain.ozf Program.ozf \
           Utils/ListDict.ozf Utils/LP.ozf Utils/Memo.ozf Utils/MList.ozf \
           Utils/MSet.ozf Utils/Set.ozf Utils/OpenMap.ozf Utils/Service.ozf\
           Utils/IntMap.ozf Utils/Debug.ozf \
           FOF/BDD.ozf FOF/FOF.ozf FOF/TermSet.ozf FOF/QuantSet.ozf \
           FOF/EQSet.ozf FOF/Binding.ozf FOF/VarMap.ozf \
           SitCalc/SitCalc.ozf SitCalc/DomainBuilder.ozf SitCalc/JointExec.ozf\
           SitCalc/MIndiGolog.ozf SitCalc/Step.ozf SitCalc/Time.ozf\
           SitCalc/Planner.ozf

%.ozf: %.oz
	ozc -c $< -o $@

%.exe: %.oz
	ozc -x $< -o $@

%.png: %.dot
	dot -o $@ -Tpng $<

%.tex: %.dot
	dot2tex --preproc $< | dot2tex --figonly > $@

goloz: Goloz.oz $(FUNCTORS)
	ozc -x $< -o goloz 

plan.dot: goloz
	./goloz

test: RunTests.exe $(FUNCTORS)
	./RunTests.exe

plan: plan.png
	gthumb plan.png &

clean:
	rm -rf *.ozf *.exe FOF/*.ozf Utils/*.ozf SitCalc/*.ozf goloz #*.dot *.png

todos:
	grep 'TODO' *.* FOF/*.* Utils/*.* SitCalc/*.*

