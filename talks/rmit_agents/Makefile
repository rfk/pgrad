

TEX2PDF = pdflatex

GRAPHICS = frame_soln.jpg poss_worlds.jpg

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.nav *.out *.snm
GARBAGE = $(LATEX_GARBAGE) *~

PDF = sc_knowledge.pdf

# Default target makes all doc types
all: $(PDF)

# Export graphics from various file formats into EPS for easy inclusion

%.jpg: %.dia
	dia -e $@ $<

# Run LaTeX a few times to generate DVI file
%.pdf: %.tex $(GRAPHICS)
	$(TEX2PDF) $<
	$(TEX2PDF) $<

##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(GRAPHICS)


