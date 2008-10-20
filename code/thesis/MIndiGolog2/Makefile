
FUNCTORS = Domain.ozf Procedures.ozf LP.ozf IntMap.ozf JointExec.ozf MIndiGolog.ozf Planner.ozf Sitcalc.ozf Step.ozf

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

all: main.exe

main.exe: main.ozf $(FUNCTORS)

plan: main.exe
	./main.exe
	make plan.png

clean:
	rm -rf *.ozf

clobber: clean
	rm -rf *.exe *.dot *.png MIndiGolog2-0.9.9.tar.gz

dist:
	mkdir MIndiGolog2-0.9.9
	cp Makefile *.txt *.oz ./MIndiGolog2-0.9.9
	tar -czvf MIndiGolog2-0.9.9.tar.gz MIndiGolog2-0.9.9
	rm -rf MIndiGolog2-0.9.9

