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

$(PDF):	$(TEX)
	pdflatex $(TEX)
	bibtex $(TARGET)
	pdflatex $(TEX)
	pdflatex $(TEX)

#$(PDF):	$(PS)
#	ps2pdf $(PS)

pdf: clean_all $(PDF)

clean:
	rm -f *~ $(PS) $(DVI) 
	rm -f *.aux *.log *.loa *.bbl *.blg *.lof *.lot 
	rm -f sections/*.aux
	rm -f *.toc *.ps .nfs* *.out

clean_all:
	rm -f *~ $(PDF) $(PS) $(DVI) 
	rm -f *.aux *.log *.loa *.bbl *.blg *.lof *.lot 
	rm -f sections/*.aux
	rm -f *.toc *.ps .nfs* *.out
