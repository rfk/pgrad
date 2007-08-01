####
#
#  Makefile for generating thesis document, or parts thereof.
#
#  The main thesis document is thesis.tex, with individual chapters stored
#  in separate latex files and listed in $CHAPTERS.  We use pdflatex for
#  building our output files.  Here are some useful targets:
#
#    all:  create PDF for the entire thesis document
#    <chapter>.ch.pdf:  create PDF for a specific chapter
#
#    sp:   spell-check the entire thesis
#    sp-<chapter>: spell-check a specific chapter
#
#    wc:   count words over the entire thesis
#    wc-<chapter>:   count words in a specific chapter
#
#    view: built entire thesis, then view it as a pdf
#
#  Note that these wordcounts are not terribly accurate. I'll
#  try to work on that in the future...
#    

## File Lists
## Adjust $GARBAGE to add extra files for deletion in `make clean`

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.mtc* *.bbl *.blg *.bmt
GARBAGE = $(LATEX_GARBAGE) *~ *.ch.tex

CLOBBERAGE = *.ch.pdf

CHAPTERS = intro.tex background.tex golog.tex mindigolog.tex reasoning.tex knowledge.tex planning.tex discussion.tex conclusion.tex 
APPENDICES = app_code.tex proofs.tex

## Additional variables

LTX = latex -interaction=nonstopmode
BTX = bibtex -terse
PDFLTX = pdflatex
VIEWER = evince

## Basic Dependencies

all: thesis.pdf
#
# Run LaTeX a few times to generate DVI file, and get refs etc correct
%.dvi: %.tex
	$(LTX) $<
	$(LTX) $<
	$(BTX) $* || true
	$(LTX) $<
	$(LTX) $<
	$(BTX) $* || true
	$(LTX) $<

# Generate a temporary latex file that will built a single chapter
%.ch.tex: %.tex
	echo '\include{preamble}' > $@
	echo '\begin{document}' >> $@
	echo -n '\include{' >> $@
	echo -n $* >> $@
	echo '}' >> $@
	echo '\include{bibcmds}' >> $@
	echo '\end{document}' >> $@

# Generate a temporary latex file that will build a single chapter,
# without bibliography
%.nb.ch.tex: %.tex
	echo '\include{preamble}' > $@
	echo '\begin{document}' >> $@
	echo -n '\include{' >> $@
	echo -n $* >> $@
	echo '}' >> $@
	echo '\end{document}' >> $@

# DVI converters for different formats
%.ps: %.dvi
	dvips -o $@ $<

%.pdf: %.dvi
	$(PDFLTX) $*.tex

##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(PS) $(HTML) $(RTF) $(CLOBBERAGE)


## Other Misc Commands

# counting words in a latex file, from http://wlug.org.nz/LatexWordcount
wc:  thesis.dvi
	dvi2tty -w100 thesis.dvi | perl -pe 's/-$$// || s/$$/ /; chomp; s/[-\._|]//g' | wc -w

wc-%: %.nb.ch.dvi
	dvi2tty -w100 $< | perl -pe 's/-$$// || s/$$/ /; chomp; s/[-\._|]//g' | wc -w

# spellchecking each individual file with aspell
sp:
	aspell -t -c thesis.tex
	for FN in $(CHAPTERS); do aspell -t -c $$FN; done;
	for FN in $(APPENDICES); do aspell -t -c $$FN; done;

sp-%: %.tex
	aspell -t -c $<

# easy viewing of entire thesis
view: thesis.pdf
	$(VIEWER) thesis.pdf &


##  Specific dependenices

thesis.dvi: thesis.tex $(CHAPTERS) $(APPENDICES)


