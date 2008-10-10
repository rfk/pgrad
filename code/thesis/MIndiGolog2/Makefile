
FUNCTORS = Domain.ozf Procedures.ozf LP.ozf Control.ozf IntMap.ozf JointExec.ozf MIndiGolog.ozf Planner.ozf Sitcalc.ozf Step.ozf

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

plans: plan.png plan_jim.png plan_joe.png plan_jon.png
	gthumb plan*.png &

clean:
	rm -rf *.ozf

clobber: clean
	rm -rf *.exe *.dot *.png

