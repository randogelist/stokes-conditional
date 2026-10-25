.PHONY: all clean
all: generalized_fefferman_preprint.pdf

generalized_fefferman_preprint.pdf: generalized_fefferman_preprint.tex
	pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape generalized_fefferman_preprint.tex
	pdflatex -interaction=nonstopmode -halt-on-error -no-shell-escape generalized_fefferman_preprint.tex

clean:
	rm -f generalized_fefferman_preprint.aux generalized_fefferman_preprint.log generalized_fefferman_preprint.out
