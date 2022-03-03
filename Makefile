build_options = -D ./ -j 4 -v

FIGDIR := ./document/figs

fig-%.pdf:  fig-%.tex
	pdflatex -output-directory=$(FIGDIR) $<

PDFs = $(addsuffix .pdf, $(basename $(wildcard $(FIGDIR)/fig-*.tex)))

properly:
	isabelle build $(build_options)

qnd: $(PDFs)
	isabelle build -o quick_and_dirty $(build_options)
