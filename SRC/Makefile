default: all
all: view

MAIN=src
STYLE=stylish.fmt

view: $(MAIN).pdf
	evince --class='TexEvince' $(MAIN).pdf

$(MAIN).pdf: $(STYLE) $(MAIN).lagda
	lhs2TeX --poly -o $(MAIN).tex $(MAIN).lagda
	xelatex $(MAIN).tex
	bibtex $(MAIN).aux

clean:
	rm -f *.aux *.log *.out *.bbl *.lof *.blg *.lot *.pyg *.gz *.toc *.ptb *.dvi $(MAIN).tex $(MAIN).pdf

.PHONY: default all clean view
