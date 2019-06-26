MAIN=tyde
STYLE=stylish.fmt

default: all
all: $(MAIN).pdf

redo:
	xelatex $(MAIN).tex
	bibtex $(MAIN).aux

$(MAIN).pdf: $(MAIN).tex
	xelatex $(MAIN).tex
	bibtex $(MAIN).aux

%.tex : %.lagda $(STYLE)
	lhs2TeX --poly -o $@ $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi $(MAIN).tex $(MAIN).pdf

.PHONY: default all clean redo
