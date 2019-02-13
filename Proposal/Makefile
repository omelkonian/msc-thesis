default: all

all: build

build: code.lagda
	agda --latex-dir=. --latex code.lagda

clean:
	rm -f *.agdai *.aux *.log l*.out code.tex

.PHONY: default all clean
