

FUNCTORS = Domain.ozf Time.ozf Sitcalc.ozf MIndiGolog.ozf Procedures.ozf LP.ozf Control.ozf

TIME_CMD = /usr/bin/time -f "%e" -a -o

all: main.exe $(FUNCTORS)

main.exe: $(FUNCTORS)


run-%-p: main.exe
	./main.exe --agent=$* --psearch

run-%-s: main.exe
	./main.exe --agent=$* --nopsearch

time-test: main.exe
	rm -f TIME.*
	./main.exe --agent=jon --psearch &
	sleep 1
	./main.exe --agent=jim --psearch &
	sleep 1
	$(TIME_CMD) TIME.p ./main.exe --agent=joe --psearch
	./main.exe --agent=jon --nopsearch &
	sleep 1
	./main.exe --agent=jim --nopsearch &
	sleep 1
	$(TIME_CMD) TIME.s ./main.exe --agent=joe --nopsearch
	./main.exe --agent=jon --psearch &
	sleep 1
	./main.exe --agent=jim --psearch &
	sleep 1
	$(TIME_CMD) TIME.p ./main.exe --agent=joe --psearch
	./main.exe --agent=jon --nopsearch &
	sleep 1
	./main.exe --agent=jim --nopsearch &
	sleep 1
	$(TIME_CMD) TIME.s ./main.exe --agent=joe --nopsearch
	./main.exe --agent=jon --psearch &
	sleep 1
	./main.exe --agent=jim --psearch &
	sleep 1
	$(TIME_CMD) TIME.p ./main.exe --agent=joe --psearch
	./main.exe --agent=jon --nopsearch &
	sleep 1
	./main.exe --agent=jim --nopsearch &
	sleep 1
	$(TIME_CMD) TIME.s ./main.exe --agent=joe --nopsearch

%.ozf: %.oz
	ozc -g -p -c $< -o $@

%.exe: %.oz
	ozc -g -p -x $< -o $@

clean:
	rm -rf *.ozf *.exe *.ozf 

dist:
	mkdir MIndiGolog1
	cp Makefile *.txt *.oz ./MIndiGolog1
	tar -czvf MIndiGolog1.tar.gz MIndiGolog1
	rm -rf MIndiGolog1

