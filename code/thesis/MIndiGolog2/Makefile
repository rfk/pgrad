
FUNCTORS = Domain.ozf Procedures.ozf LP.ozf Control.ozf IntMap.ozf JointExec.ozf MIndiGolog.ozf Planner.ozf Sitcalc.ozf Step.ozf

%.ozf: %.oz
	ozc -p -c $< -o $@

%.exe: %.oz
	ozc -p -x $< -o $@

%.png: %.dot
	dot -o $@ -Tpng $<

%.dia: %.dot
	dot -o $@ -Tdia $<

%.svg: %.dot
	dot -o $@ -Tsvg $<

%.tex: %.dot
	dot2tex --preproc $< | dot2tex --figonly > $@

all: main.exe

main.exe: main.ozf $(FUNCTORS)

plans: main.exe
	./main.exe
	make plan.png
	make plan.dia
	gthumb plan*.png &

clean:
	rm -rf *.ozf

clobber: clean
	rm -rf *.exe *.dot *.png
dist:
	mkdir MIndiGolog2
	cp Makefile *.txt *.oz ./MIndiGolog2
	tar -czvf MIndiGolog2.tar.gz MIndiGolog2
	rm -rf MIndiGolog2



