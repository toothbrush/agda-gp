LHS_FILE=$(wildcard *.lagda)
TEX_FILE=$(LHS_FILE:.lagda=.tex)
FMTS=$(wildcard *.fmt)

all: pdf

pdf: $(TEX_FILE)
	pdflatex $(TEX_FILE)
	pdflatex $(TEX_FILE)

$(TEX_FILE): $(LHS_FILE) $(FMTS)
	@echo $(LHS_FILE)
	lhs2TeX --agda $(LHS_FILE) > $(TEX_FILE)

pdfshow: pdf
	if [ -x /usr/bin/open ] ; then open $(TEX_FILE:.tex=.pdf); fi
	if [ -x /usr/bin/xpdf ] ; then xpdf $(TEX_FILE:.tex=.pdf); fi &

.PHONY: pdfshow
