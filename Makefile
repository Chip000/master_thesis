TARGET=tese

TEX=$(TARGET).tex
DVI=$(TARGET).dvi
PS=$(TARGET).ps
PDF=$(TARGET).pdf

.PHONY: pdf clean

$(DVI): $(TEX)
	latex $(TEX)
	bibtex $(TARGET)
	latex $(TEX)
	latex $(TEX)

$(PS): $(DVI)
	dvips -mz $(TARGET).dvi

$(PDF): $(PS)
	ps2pdf $(PS)

pdf: clean $(PDF)

clean:
	rm -f *~ $(PDF) $(PS) $(DVI) 
	rm -f *.aux *.log *.loa *.bbl *.blg *.lof *.lot 
	rm -f sections/*.aux
	rm -f *.toc *.ps .nfs* *.out

