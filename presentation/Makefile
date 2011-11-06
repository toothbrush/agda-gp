LHS_FILE=$(wildcard *.lagda)
TEX_FILE=$(LHS_FILE:.lagda=.tex)
ADOBE_PATH="/cygdrive/c/Program Files (x86)/Adobe/Reader 10.0/Reader/AcroRd32.exe"

all: slides notes

slides: $(TEX_FILE)
	pdflatex slides.$(TEX_FILE)
	pdflatex slides.$(TEX_FILE)

notes: $(TEX_FILE)
	pdflatex notes.$(TEX_FILE)
	pdflatex notes.$(TEX_FILE)

$(TEX_FILE): $(LHS_FILE)
	@echo $(LHS_FILE)
	lhs2TeX --agda $(LHS_FILE) > $(TEX_FILE)

 pdfshow: notes
	if [ -x /usr/bin/open ] ; then open notes.$(TEX_FILE:.tex=.pdf); fi
	if [ -x /usr/bin/xpdf ] ; then xpdf notes.$(TEX_FILE:.tex=.pdf); fi &
	if [ -x $(ADOBE_PATH) ] ; then $(ADOBE_PATH) notes.$(TEX_FILE:.tex=.pdf); fi &

.PHONY: pdfshow pdf $(TEX_FILE)
