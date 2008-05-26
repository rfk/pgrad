
LTX = latex -interaction=nonstopmode
BTX = bibtex -terse
LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.mtc* *.bbl *.blg *.bmt *.maf *.bak 
GARBAGE = $(LATEX_GARBAGE) *~ KR08KellyR92


KR08KellyR92.tar.gz: kr08.pdf
	# Cleanout and re-create target directory
	rm -rf KR08KellyR92.tar.gz ./KR08KellyR92
	mkdir ./KR08KellyR92
	# Main PDF File
	cp kr08.pdf ./KR08KellyR92/Kelly.pdf
	# Main source file with included bibliography
	LN=`grep -n 'bibliography{' kr08.tex | head -n 1 | cut -f 1 -d ':'` && cat kr08.tex | head -n `expr $$LN - 1` > KR08KellyR92/Kelly.tex
	cat kr08.bbl >> KR08KellyR92/Kelly.tex
	LN=`grep -n 'bibliography{' kr08.tex | head -n 1 | cut -f 1 -d ':'` && cat kr08.tex | tail -n +`expr $$LN + 1`  >> KR08KellyR92/Kelly.tex
	# Supporting style files
	# OK, tar them up
	tar -czvf KR08KellyR92.tar.gz KR08KellyR92/

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf KR08KellyR92.tar.gz kr08.pdf kr08.tex

%.tex: %.lyx
	lyx -e latex $<

%.dvi: %.tex
	$(LTX) $<
	$(LTX) $<
	$(BTX) $* || true
	$(LTX) $<
	$(LTX) $<
	$(BTX) $* || true
	$(LTX) $<

%.pdf: %.dvi
	pdflatex $*.tex

