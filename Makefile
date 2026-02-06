.PHONY: all lean part1 part3 clean

all: lean part1

lean:
	cd lean && lake build

part1: part1/paper.pdf

part3: part3/paper.pdf

part1/paper.pdf: part1/paper.tex cred.bib part1/figures/path_dependence.pdf
	cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

part3/paper.pdf: part3/paper.tex cred.bib
	cd part3 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

clean:
	cd part1 && latexmk -C
	cd part3 && latexmk -C
