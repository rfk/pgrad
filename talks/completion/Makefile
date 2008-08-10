
TEX2PDF = pdflatex

GRAPHICS = 

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.nav *.out *.snm
GARBAGE = $(LATEX_GARBAGE) *~

PDF = async_sitcalc.pdf

# Default target makes all doc types
all: $(PDF)

%.png: %.dia
	dia -e $@ $<

%.pdf: %.tex
	$(TEX2PDF) $<
	$(TEX2PDF) $<
	$(TEX2PDF) $<

view:	$(PDF)
	evince $(PDF)

async_sitcalc.pdf:  $(GRAPHICS)

##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(GRAPHICS)


