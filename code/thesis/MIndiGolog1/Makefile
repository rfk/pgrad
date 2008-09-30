

FUNCTORS = Domain.ozf Time.ozf Sitcalc.ozf MIndiGolog.ozf Procedures.ozf LP.ozf Control.ozf

TIME_CMD = /usr/bin/time -f "%e" -a -o

all: main.exe $(FUNCTORS)

run-%: main.exe
	./main.exe --agent=$* --psearch

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

run-serial: main.exe
	./main.exe --agent=jon &
	sleep 1
	./main.exe --agent=jim &
	sleep 1
	./main.exe --agent=joe

run-parallel: main.exe
	./main.exe --agent=jon --psearch &
	sleep 1
	./main.exe --agent=jim --psearch &
	sleep 1
	./main.exe --agent=joe --psearch

%.ozf: %.oz
	ozc -g -p -c $< -o $@

%.exe: %.oz
	ozc -g -p -x $< -o $@

clean:
	rm -rf *.ozf *.exe *.ozf 

main.exe: $(FUNCTORS)

