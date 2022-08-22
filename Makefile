main: Main.lhs
	lhs2TeX --agda Main.lhs -o Main.tex
	pdflatex Main.tex

bib: Main.lhs
	lhs2TeX --agda Main.lhs -o Main.tex
	pdflatex Main.tex
	biber Main
	pdflatex Main.tex

.PHONY: clean
clean:
	rm Main.tex *.aux *.nav *.log *.out *.snm *.ptb *.toc *.vrb
