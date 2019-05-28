default: all

all: view

view: build
	evince src.pdf &

build: code src.tex
	xelatex -interaction=nonstopmode --shell-escape src.tex
	bibtex src.aux
	xelatex -interaction=nonstopmode --shell-esacpe src.tex

code: stylish.lhs src.lagda
	lhs2TeX --poly -o src.tex src.lagda

clean:
	rm -f *.aux *.log *.out *.ptb *.blg *.bbl code.tex

.PHONY: default all clean
