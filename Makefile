.PHONY: all lean part1 part2 part3 part4 part5 part6 part7 clean

all: lean part1 part2 part3 part4 part5 part6 part7

lean:
	cd lean && lake build

part1: part1/paper.pdf

part2: part2/paper.pdf

part3: part3/paper.pdf

part4: part4/paper.pdf

part5: part5/paper.pdf

part6: part6/paper.pdf

part7: part7/paper.pdf

part1/paper.pdf: part1/paper.tex cred.bib part1/figures/path_dependence.pdf
	cd part1 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

part2/paper.pdf: part2/paper.tex cred.bib
	cd part2 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

part3/paper.pdf: part3/paper.tex cred.bib
	cd part3 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

part4/paper.pdf: part4/paper.tex cred.bib
	cd part4 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

part5/paper.pdf: part5/paper.tex cred.bib
	cd part5 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

part6/paper.pdf: part6/paper.tex cred.bib
	cd part6 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

part7/paper.pdf: part7/paper.tex cred.bib
	cd part7 && latexmk -pdf -interaction=nonstopmode -halt-on-error paper.tex

clean:
	cd part1 && latexmk -C
	cd part2 && latexmk -C
	cd part3 && latexmk -C
	cd part4 && latexmk -C
	cd part5 && latexmk -C
	cd part6 && latexmk -C
	cd part7 && latexmk -C
