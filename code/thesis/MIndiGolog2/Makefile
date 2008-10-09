

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
	ozc -p -c $< -o $@

%.exe: %.oz
	ozc -p -x $< -o $@

%.png: %.dot
	dot -o $@ -Tpng $<

%.tex: %.dot
	dot2tex --preproc $< | dot2tex --figonly > $@

all: main.exe
main.exe: main.ozf $(FUNCTORS)

plan.dot: main.exe
	./main.exe

test: RunTests.exe $(FUNCTORS)
	./RunTests.exe

plan: plan.png
	gthumb plan.png &

clean:
	rm -rf *.ozf FOF/*.ozf Utils/*.ozf SitCalc/*.ozf

clobber: clean
	rm -rf *.exe *.dot *.png

todo:
	grep 'TODO' *.* FOF/*.* Utils/*.* SitCalc/*.*

