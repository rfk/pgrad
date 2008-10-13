#
#  Makefile for generating thesis document, or parts thereof.
#
#  The main thesis document is thesis.tex, with individual chapters stored
#  in separate latex files and listed in $CHAPTERS.  We use pdflatex for
#  building our output files.  Here are some useful targets:
#
#    all:  create PDF for the entire thesis document
#    <chapter>.ch.pdf:  create PDF for a specific chapter
#    <chapter>.nb.ch.pdf:  create PDF for a specific chapter, without biblio
#
#    view: built entire thesis, then view it as a pdf
#    view-<chapter>:  view PDF of a specific chapter
#
#    sp:   spell-check the entire thesis
#    sp-<chapter>: spell-check a specific chapter
#
#    wc:   count words over the entire thesis
#    wc-<chapter>:   count words in a specific chapter
#
#    edit-<chapter>:  launch LyX to edit a chapter
#
#    publish:  upload thesis to CS website
#
#  Note that the wordcounts are not terribly accurate. I'll
#  try to work on that in the future...
#    

## File Lists
## Adjust $GARBAGE to add extra files for deletion in `make clean`

LATEX_GARBAGE = *.aux *.lof *.dvi *.log *.toc *.lot *.mtc* *.bbl *.blg *.bmt *.maf *.loa
GARBAGE = $(LATEX_GARBAGE) *~ *.ch.tex *.ed.tex *.ed.lyx rawchapters.tex *.bak

CLOBBERAGE = thesis.pdf *.ch.pdf *.tmp.pdf rawchapters.pdf ./upload-thesis/

CHAPTERS = abstract.tex intro.tex background.tex mindigolog.tex observations.tex jointexec.tex persistence.tex knowledge.tex cknowledge.tex conclusion.tex 
APPENDICES = implementation.tex proofs.tex
AUXFILES = preamble.tex mathmacros.tex bibcmds.tex
LISTINGS_PDF = listings/jointexec/example_je.pdf listings/jointexec/example_pes.pdf listings/jointexec/unfeas_je.pdf listings/jointexec/unfeas_je2.pdf listings/jointexec/salad2_plan.pdf listings/jointexec/salad1_plan.pdf
LISTINGS_EPS = listings/jointexec/example_je.eps listings/jointexec/example_pes.eps listings/jointexec/unfeas_je.eps listings/jointexec/unfeas_je2.eps listings/jointexec/salad2_plan.eps listings/jointexec/salad1_plan.eps

## Additional variables

#LTX = latex -interaction=nonstopmode
LTX = latex 
BTX = bibtex -terse
PDFLTX = pdflatex
VIEWER = evince
SPELLCHECK = aspell -l en_GB -t --add-tex-command="bibentry p" --add-tex-command="citep p" --add-tex-command="citet p" -c

## Basic Dependencies

all: thesis.pdf

# Run LaTeX a few times to generate DVI file, and get refs etc correct
%.dvi: %.tex
	$(LTX) $<
	$(LTX) $<
	$(BTX) $* || true
	$(LTX) $<
	$(LTX) $<
	$(BTX) $* || true
	$(LTX) $<

# Generate a temporary latex file that will build a single chapter
%.ch.tex: %.tex
	cat preamble.tex > $@
	# Doing echo '\begin{document}' works on my PC, but prints
	# a weird metacharacter on my laptop.  WTF?
	echo -n '\' >> $@
	echo 'begin{document}' >> $@
	cat mathmacros.tex >> $@
	echo -n '\' >> $@
	echo 'onehalfspace' >> $@
	cat $< >> $@
	cat bibcmds.tex >> $@
	echo -n '\' >> $@
	echo 'end{document}' >> $@

abstract.ch.pdf: abstract.ch.tex abstract.ch.dvi
	$(PDFLTX) abstract.ch.tex

NUM_LEADING_PAGES = 16

%.ch.pdf: thesis.pdf
	rm -f rawchapters.aux *.ch.aux
	for CHAP in $(CHAPTERS) references.tex $(APPENDICES); do if [ "$$LASTCHAP" = "$*.tex" ]; then NEXTCHAP=`basename $$CHAP .tex`; fi; LASTCHAP=$$CHAP; done && echo N_$$NEXTCHAP && PGNUM_S=`grep "\\newlabel{ch:$*}" * | cut -d '{' -f 5 | tr -d '}'` && echo S_$$PGNUM_S && PGNUM_S=`expr $$PGNUM_S + $(NUM_LEADING_PAGES)` && echo S_$$PGNUM_S && if [ "$$NEXTCHAP"x = "x" ]; then PGNUM_E=`grep "Output written" thesis.log | cut -d '(' -f 2 | cut -d ' ' -f 1` && echo E_$$PGNUM_E; else PGNUM_E=`grep "\\newlabel{ch:$$NEXTCHAP}" * | cut -d '{' -f 5 | tr -d '}'` && echo E_$$PGNUM_E && PGNUM_E=`expr $$PGNUM_E + $(NUM_LEADING_PAGES) - 1` && echo E_$$PGNUM_E ; fi && echo $$PGNUM_S-$$PGNUM_E && pdfnup --nup 1x1 --pages $$PGNUM_S-$$PGNUM_E --outfile $@ thesis.pdf
	

# Generate a temporary latex file that will build a single chapter,
# without bibliography
%.nb.ch.tex: %.tex
	cat preamble.tex > $@
	echo -n '\' >> $@
	echo 'begin{document}' >> $@
	cat mathmacros.tex >> $@
	echo -n '\' >> $@
	echo 'onehalfspace' >> $@
	cat $< >> $@
	echo -n '\' >> $@
	echo 'end{document}' >> $@

rawchapters.tex: $(CHAPTERS)
	cat preamble.tex > $@
	echo -n '\' >> $@
	echo 'begin{document}' >> $@
	cat mathmacros.tex >> $@
	echo -n '\' >> $@
	echo 'onehalfspace' >> $@
	for FN in $(CHAPTERS); do cat $$FN >> $@; done;
	echo -n '\' >> $@
	echo 'end{document}' >> $@

# DVI converters for different formats
%.ps: %.dvi
	dvips -o $@ $<

%.pdf: %.dvi
	$(PDFLTX) $*.tex

# Graphics converters

%.png: %.dia
	dia -e $@ $<

%.eps: %.dia
	dia -e $@ $<

%.pdf: %.eps
	epstopdf $<

##  Cleanup Commands

clean:
	rm -rf $(GARBAGE)

clobber: clean
	rm -rf $(CLOBBERAGE)


## Other Misc Commands

# counting words in a latex file, from http://wlug.org.nz/LatexWordcount
wc:  rawchapters.dvi
	dvi2tty -w100 rawchapters.dvi | perl -pe 's/-$$// || s/$$/ /; chomp; s/[-\._|]//g' | wc -w

wc-%: %.nb.ch.dvi
	dvi2tty -w100 $< | perl -pe 's/-$$// || s/$$/ /; chomp; s/[-\._|]//g' | wc -w

# spellchecking each individual file with aspell
sp:
	$(SPELLCHECK) thesis.tex
	for FN in $(CHAPTERS); do $(SPELLCHECK) $$FN; done;
	for FN in $(APPENDICES); do $(SPELLCHECK) $$FN; done;

sp-%: %.tex
	$(SPELLCHECK) $<

# easy viewing of entire thesis
view: thesis.pdf
	$(VIEWER) thesis.pdf &

view-%: %.ch.pdf
	cp $< $<.tmp.pdf
	$(VIEWER) $<.tmp.pdf &

# easy editing of chapters in lyx
edit-%: %.ch.tex
	# Fail if already editing
	if [ -f $*.ed.lyx ] ; then false ; fi
	# Generate lyx file from the latex
	rm -rf $*.ed.lyx $*.ed.tex
	tex2lyx -c thesis $< $*.ed.lyx
	# Run lyx for editing, then export back to latex
	lyx $*.ed.lyx
	lyx --export latex $*.ed.lyx
	# Remove LyX cruft
	python aux/unlyx.py < $*.ed.tex > $*.tex
	rm $*.ed.lyx $*.ed.tex


# publish latest versions to my CSSE website
publish:
	make thesis.pdf
	for FN in $(CHAPTERS); do make `basename $$FN .tex`.ch.pdf; done;
	for FN in $(APPENDICES); do make `basename $$FN .tex`.ch.pdf; done;
	make references.ch.pdf
	mkdir upload-thesis
	cp *.pdf ./upload-thesis/
	tar -czvf upload-thesis/thesis.tar.gz *.tex Makefile listings
	tar -czvf upload-thesis.tar.gz upload-thesis
	scp upload-thesis.tar.gz rfk@mundula.cs.mu.oz.au:
	ssh mundula.cs.mu.oz.au 'gunzip upload-thesis.tar.gz && cd www_public && tar -xvf ~/upload-thesis.tar && mv upload-thesis/* thesis/ && rm -r upload-thesis ~/upload-thesis.tar && chmod 755 thesis && chmod 644 thesis/*'
	rm -rf upload-thesis upload-thesis.tar.gz

# find things left to do
todo:
	grep --color -i todo *.*

# find latex/bibtex warnings
warnings: thesis.dvi
	grep --color '^Warning' thesis.blg || true
	echo ""
	grep --color 'Warning' thesis.log || true
	echo ""
	grep --color -A 1 '^Overfull' thesis.log || true


##  Specific dependenices

thesis.dvi: thesis.tex $(AUXFILES) $(CHAPTERS) $(APPENDICES) ../../library/references.bib $(LISTINGS_EPS)

thesis.pdf: $(LISTINGS_PDF)

listings: $(LISTINGS_PDF) $(LISTINGS_EPS)


