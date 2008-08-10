
PLTX = pdflatex
BTX = bibtex -terse

GRAPHICS = poss_worlds.png k_relation.png frame_soln.png

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.nav *.out *.snm
GARBAGE = $(LATEX_GARBAGE) *~

PDF = async_sitcalc.pdf

# Default target makes all doc types
all: $(PDF)

%.png: %.dia
	dia -e $@ $<

%.pdf: %.tex
	$(PLTX) $< || rm -f $*.pdf
	$(BTX) $* || true
	$(PLTX) $< || rm -f $*.pdf
	$(BTX) $* || true
	$(PLTX) $<

view:	$(PDF)
	evince $(PDF)

async_sitcalc.pdf:  $(GRAPHICS)

##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(GRAPHICS)


