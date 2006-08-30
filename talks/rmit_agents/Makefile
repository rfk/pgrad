

TEX2PDF = pdflatex

GRAPHICS = frame_soln.jpg poss_worlds.jpg

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.nav *.out *.snm
GARBAGE = $(LATEX_GARBAGE) *~

PDF = sc_knowledge.pdf

# Default target makes all doc types
all: $(PDF)

%.jpg: %.dia
	dia -e $@ $<

%.pdf: %.tex $(GRAPHICS)
	$(TEX2PDF) $<

view:	$(PDF)
	evince $(PDF)

##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(GRAPHICS)


