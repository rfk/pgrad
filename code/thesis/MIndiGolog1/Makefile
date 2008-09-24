

FUNCTORS = Domain.ozf Time.ozf Sitcalc.ozf MIndiGolog.ozf Procedures.ozf LP.ozf


all: main.exe $(FUNCTORS)

run: main.exe
	./main.exe

%.ozf: %.oz
	ozc -g -p -c $< -o $@

%.exe: %.oz
	ozc -g -p -x $< -o $@

clean:
	rm -rf *.ozf *.exe *.ozf 

main.exe: $(FUNCTORS)

