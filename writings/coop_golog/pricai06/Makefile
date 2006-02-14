
##
##  Makefile to produce paper from latex
##

## Macro Definitions
#
#  The following define the programs to use to generate various documentation
#  types, as follows:
#
#    * HTML:		latex2html
#    * PostScript:	dvips 
#    * PDF:		dvipdf 
#
#  Command-line options can be added/changed here, or other software with a
#  compatible interface can be substituted.

L2H = latex2html -split 0 -show_section_numbers -toc_depth 5 -ascii_mode -images
DVIPS = dvips
DVIPDFM = dvipdfm
L2RTF = latex2rtf


## File Lists

# Images to be included in each document.  The _CLEAN list should be those
# which are generated from other source images and may be deleted by cleaning

IMAGES_CLEAN = 	

IMAGES = 

LISTINGS =


## Adjust $GARBAGE to add extra files for deletion in `make clean`
LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.bbl *.blg
GARBAGE = $(LATEX_GARBAGE) *~ $(IMAGES_CLEAN)

PS = pricai06.ps
PDF = prica06.pdf
RTF = # List RTF files
HTML = # List HTML Files


## Basic Dependencies

# Default target makes all doc types
all: ps pdf html rtf

ps: $(PS)
pdf: $(PDF)
html: $(HTML)
rtf: $(RTF)

#
# Export graphics from various file formats into EPS for easy inclusion

%.eps: %.dia
	dia -e $@ $<

%.eps: %.jpg
	convert $< $@

%.eps: %.png
	convert $< $@

%.eps: %.bmp
	convert $< $@


# Export from LyX to LaTeX
%.tex: %.lyx
	lyx -e latex $<

# Generate bibtex files
%.bbl: %.tex
	latex $<
	bibtex $*

# Run LaTeX a few times to generate DVI file
%.dvi: %.tex
	latex $<
	latex $<
	latex $<


# DVI converters for different formats
%.ps: %.dvi
	$(DVIPS) -o $@ $<

%.pdf: %.dvi
	$(DVIPDFM) -o $@ $<

%/index.html: %.tex
	$(L2H) $<

%.rtf: %.dvi
	$(L2RTF) $*.tex


##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(PS) $(HTML) $(RTF)


##  Additional Dependencies

prica06.dvi:  $(IMAGES) $(LISTINGS) prica06.bbl ../../../library/references.bib

view:   clobber pricai06.pdf
	evince pricai06.pdf

