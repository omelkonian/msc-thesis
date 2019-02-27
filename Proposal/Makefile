default: all

all: build

build: code.lagda
	lhs2TeX --poly -o code.tex code.lagda

clean:
	rm -f *.aux *.log l*.out code.tex

.PHONY: default all clean
