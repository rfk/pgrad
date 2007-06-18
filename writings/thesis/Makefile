
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
PDFLT = pdflatex
L2RTF = latex2rtf


## File Lists
## Adjust $GARBAGE to add extra files for deletion in `make clean`

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.mtc* *.bbl *.blg *.bmt
GARBAGE = $(LATEX_GARBAGE) *~

PS =  # List PS Files
PDF = thesis.pdf # List PDF Files
RTF = # List of RTF Files
HTML = # List HTML Files

CHAPTERS = intro.tex background.tex conclusion.tex implementation.tex knowledge.tex mindigolog.tex offline_exec.tex online_exec.tex reasoning.tex abstract.tex


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


# Export from LyX to LaTeX
%.tex: %.lyx
	lyx -e latex $<

# Run LaTeX a few times to generate DVI file
%.dvi: %.tex
	latex $<
	latex $<
	bibtex $*
	latex $<
	latex $<
	bibtex $*
	latex $<


# DVI converters for different formats
%.ps: %.dvi
	$(DVIPS) -o $@ $<

%.pdf: %.dvi
	$(PDFLT) $*.tex

%/index.html: %.tex
	$(L2H) $<

%.rtf: %.dvi
	$(L2RTF) $*.tex


##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(PDF) $(PS) $(HTML) $(RTF)


## Other Misc Commands

view:  thesis.pdf
	evince thesis.pdf &

# counting words in a latex file, from http://wlug.org.nz/LatexWordcount
wc:  thesis.dvi
	dvi2tty -w100 thesis.dvi | perl -pe 's/-$$// || s/$$/ /; chomp; s/[-\._|]//g' | wc -w

# spellchecking each individual file with aspell
sp:
	aspell -t -c thesis.tex
	for FN in $(CHAPTERS); do aspell -t -c $$FN; done;

##  Specific dependenices

thesis.dvi: thesis.tex $(CHAPTERS)


