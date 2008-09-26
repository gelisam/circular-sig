all: paper.pdf
.PHONY: all clean clobber

%.pdf: %.tex paper.bib
	pdflatex -interaction=nonstopmode $<
	bibtex paper
	pdflatex -interaction=nonstopmode $<
	pdflatex -interaction=nonstopmode $<

clean:
	rm -rf paper.aux paper.log paper.bbl paper.blg

clobber: clean
	rm -rf paper.pdf
