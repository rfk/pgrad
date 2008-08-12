
PLTX = pdflatex
BTX = bibtex -terse

GRAPHICS = poss_worlds.pdf k_relation.pdf frame_soln.pdf k_unobs.pdf k_unobs_highlighted.pdf pk_regression.pdf jointexec.pdf plan.pdf

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.nav *.out *.snm *.bbl *.blg 
GARBAGE = $(LATEX_GARBAGE) *~ *.eps

PDF = async_sitcalc.pdf

# Default target makes all doc types
all: $(PDF)

%.png: %.dia
	dia -e $@ $<

%.eps: %.dia
	dia -e $@ $<

%.pdf: %.eps
	epstopdf $<

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


