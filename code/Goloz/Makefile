

FUNCTORS = Agent.ozf Domain.ozf \
           Utils/ListDict.ozf Utils/LP.ozf Utils/Memo.ozf Utils/MList.ozf \
           Utils/MSet.ozf Utils/Set.ozf Utils/OpenMap.ozf \
           FOF/BDD.ozf FOF/FOF.ozf FOF/TermSet.ozf FOF/QuantSet.ozf \
           FOF/EQSet.ozf FOF/Binding.ozf FOF/VarMap.ozf \
           SitCalc/SitCalc.ozf SitCalc/DomainBuilder.ozf SitCalc/Execution.ozf\
           SitCalc/MIndiGolog.ozf SitCalc/JointPlan.ozf SitCalc/PlanFront.ozf\
           SitCalc/Time.ozf

%.ozf: %.oz
	ozc -c $< -o $@

%.exe: %.oz
	ozc -x $< -o $@

goloz: Goloz.oz $(FUNCTORS)
	ozc -x $< -o goloz 

test: RunTests.exe $(FUNCTORS)
	./RunTests.exe

clean:
	rm -rf *.ozf *.exe FOF/*.ozf Utils/*.ozf SitCalc/*.ozf goloz

todos:
	grep 'TODO' *.* FOF/*.* Utils/*.* SitCalc/*.*

