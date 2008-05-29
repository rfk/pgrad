
LTX = latex -interaction=nonstopmode
BTX = bibtex -terse
LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.mtc* *.bbl *.blg *.bmt *.maf *.bak 
GARBAGE = $(LATEX_GARBAGE) *~ KR08KellyR92

TEXLIVE = /usr/share/texmf-texlive/tex/latex
TEXMF = /usr/share/texmf/tex/latex


KR08KellyR92.tar.gz: kr08.pdf
	# Cleanout and re-create target directory
	rm -rf KR08KellyR92.tar.gz ./KR08KellyR92
	mkdir ./KR08KellyR92
	# Main PDF File
	cp kr08.pdf ./KR08KellyR92/Kelly.pdf
	# Corresponding dvi file
	cp kr08.dvi KR08KellyR92/Kelly.dvi
	# Main source file with inline bibliography
	LN=`grep -n 'bibliography{' kr08.tex | head -n 1 | cut -f 1 -d ':'` && cat kr08.tex | head -n `expr $$LN - 1` > KR08KellyR92/Kelly.tex
	cat kr08.bbl >> KR08KellyR92/Kelly.tex
	LN=`grep -n 'bibliography{' kr08.tex | head -n 1 | cut -f 1 -d ':'` && cat kr08.tex | tail -n +`expr $$LN + 1`  >> KR08KellyR92/Kelly.tex
	# Supporting style files
	cp $(TEXLIVE)/amsmath/amsmath.sty ./KR08KellyR92/amsmath.sty
	cp $(TEXLIVE)/amsfonts/amssymb.sty ./KR08KellyR92/amssymb.sty
	cp $(TEXLIVE)/amsfonts/amsfonts.sty ./KR08KellyR92/amsfonts.sty
	cp $(TEXLIVE)/amscls/amsthm.sty ./KR08KellyR92/amsthm.sty
	cp $(TEXLIVE)/psnfss/times.sty ./KR08KellyR92/times.sty
	cp $(TEXLIVE)/psnfss/helvet.sty ./KR08KellyR92/helvet.sty
	cp $(TEXLIVE)/psnfss/courier.sty ./KR08KellyR92/courier.sty
	cp $(TEXLIVE)/base/article.sty ./KR08KellyR92/article.sty
	cp $(TEXLIVE)/graphics/graphicx.sty ./KR08KellyR92/graphicx.sty
	cp $(TEXMF)/aaai/aaai.sty ./KR08KellyR92/aaai.sty
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

