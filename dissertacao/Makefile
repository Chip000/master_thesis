TARGET=main
OUTFILE=tese.pdf

TEX=$(TARGET).tex
DVI=$(TARGET).dvi
PS=$(TARGET).ps
PDF=$(TARGET).pdf
BIB=bioinf

.PHONY: pdf clean

# PS2PDF RULES
#$(DVI): $(TEX)
#	latex $(TEX)
#	bibtex $(TARGET)
#	latex $(TEX)
#	latex $(TEX)
#
#$(PS): $(DVI)
#	dvips -mz $(TARGET).dvi
#
#$(PDF):	$(PS)
#	ps2pdf $(PS)

# PDFLATEX RULES
$(PDF):	$(TEX)
	pdflatex $(TEX) 
	bibtex $(TARGET)
	pdflatex $(TEX)
	pdflatex $(TEX)
	mv $(PDF) $(OUTFILE)

pdf: clean_all $(PDF) clean

rtf: $(TEX)
	latex2rtf -b $(BIB) -p -f0 $(TEX)

clean:
	rm -f *~ $(PS) $(DVI) $(TARGET).rtf
	rm -f *.aux *.log *.loa *.bbl *.blg *.lof *.lot 
	rm -f sections/*.aux
	rm -f *.toc *.ps .nfs* *.out

clean_all:
	rm -f *~ $(OUTFILE) $(PS) $(DVI) $(PDF) $(TARGET).rtf
	rm -f *.aux *.log *.loa *.bbl *.blg *.lof *.lot 
	rm -f sections/*.aux
	rm -f *.toc *.ps .nfs* *.out
