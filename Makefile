all: paper.pdf
.PHONY: all clean clobber

%.pdf: %.tex
	pdflatex -interaction=nonstopmode $<
	pdflatex -interaction=nonstopmode $<

clean:
	rm -rf paper.aux paper.log

clobber: clean
	rm -rf paper.pdf
