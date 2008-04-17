
TEX2PDF = pdflatex

GRAPHICS = frame_soln.png poss_worlds.png k_unobs.png k_unobs_highlighted.png \
           k_relation.png pk_relation.png

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.nav *.out *.snm
GARBAGE = $(LATEX_GARBAGE) *~

PDF = ck_ha_fp.pdf

# Default target makes all doc types
all: $(PDF)

%.png: %.dia
	dia -e $@ $<

%.pdf: %.tex
	$(TEX2PDF) $<
	#$(TEX2PDF) $<
	#$(TEX2PDF) $<

view:	$(PDF)
	evince $(PDF)

ck_ha_fp.pdf:  $(GRAPHICS)

##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(GRAPHICS)


