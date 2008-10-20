
clean:
	true

clobber: clean
	rm -rf *.exe *.dot *.png PKnows-0.9.9*

dist:
	mkdir PKnows-0.9.9
	cp Makefile *.txt *.pl ./PKnows-0.9.9
	mkdir PKnows-0.9.9/vpdl
	cp vpdl/*.ml ./PKnows-0.9.9/vpdl
	tar -czvf PKnows-0.9.9.tar.gz PKnows-0.9.9
	rm -rf PKnows-0.9.9

