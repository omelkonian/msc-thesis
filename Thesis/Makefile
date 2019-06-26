MAIN=thesis
STYLE=stylish.fmt

default: all
all: $(MAIN).pdf

redo:
	xelatex $(MAIN).tex
	bibtex $(MAIN).aux

$(MAIN).pdf: $(MAIN).tex
	xelatex $(MAIN).tex
	bibtex $(MAIN).aux

%.tex : %.lagda $(STYLE) 0.title.lagda 1.intro.lagda 2.background.lagda 3.methodology.lagda 4.utxo.lagda 5.bitml.lagda 6.related-work.lagda 7.future-work.lagda 8.conclusion.lagda 9.appendix.lagda
	lhs2TeX --poly -o $@ $<

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi $(MAIN).tex $(MAIN).pdf

.PHONY: default all clean redo
