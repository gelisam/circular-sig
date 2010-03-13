NAME=paper

all: $(NAME).pdf
.PHONY: all clean clobber

%.pdf: %.tex $(NAME).bib
	pdflatex -interaction=nonstopmode $<
	bibtex $(NAME)
	pdflatex -interaction=nonstopmode $<
	pdflatex -interaction=nonstopmode $<

clean:
	rm -rf $(NAME).aux $(NAME).log $(NAME).bbl $(NAME).blg

clobber: clean
	rm -rf $(NAME).pdf
