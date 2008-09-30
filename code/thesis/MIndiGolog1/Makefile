

FUNCTORS = Domain.ozf Time.ozf Sitcalc.ozf MIndiGolog.ozf Procedures.ozf LP.ozf Control.ozf

TIME_CMD = /usr/bin/time -f "%e" -o

all: main.exe $(FUNCTORS)

run-%: main.exe
	./main.exe --agent=$*

run-time-test: main.exe
	rm TIME.*
	./main.exe --agent=jon --nopsearch &
	sleep 2
	./main.exe --agent=jim --nopsearch &
	sleep 2
	$(TIME_CMD) TIME.np1 ./main.exe --agent=joe --nopsearch
	./main.exe --agent=jon --psearch &
	sleep 2
	./main.exe --agent=jim --psearch &
	sleep 2
	$(TIME_CMD) TIME.p1 ./main.exe --agent=joe --psearch
	./main.exe --agent=jon --nopsearch &
	sleep 2
	./main.exe --agent=jim --nopsearch &
	sleep 2
	$(TIME_CMD) TIME.np2 ./main.exe --agent=joe --nopsearch
	./main.exe --agent=jon --psearch &
	sleep 2
	./main.exe --agent=jim --psearch &
	sleep 2
	$(TIME_CMD) TIME.p2 ./main.exe --agent=joe --psearch

%.ozf: %.oz
	ozc -g -p -c $< -o $@

%.exe: %.oz
	ozc -g -p -x $< -o $@

clean:
	rm -rf *.ozf *.exe *.ozf 

main.exe: $(FUNCTORS)

