## Makefile for LaTeX
## 
## Copyright (c) 2001 Achim D. Brucker <brucker@informatik.uni-freiburg.de>
## All rights reserved.
## 
## This program is free software; you can redistribute it and/or modify 
## it under the terms of the GNU General Public License as published by 
## the Free Software Foundation; either version 2 of the License, or 
## (at your option) any later version.
##
## $Id: Makefile,v 1.11 2002/10/31 15:50:04 brucker Exp $
## 
## 1) Document specific configuration
## ==================================
BASEDIR      = ~/publications
BIBFILES     = 
BSTFILES     =
PIC          = 
DOCUMENT     = root
SOURCES      = 
AUTHOR       =
DIRECTORIES  = 
##
## 2) LaTeX specific Path configuration
## ====================================
TEXMFHOME      = {$(PWD)/${BASEDIR}/texmf/}
##
## 3) Configure default target
## ===========================
## this should be one of ${DOCUMENT}.dvi, ${DOCUMENT}.ps, ${DOCUMENT}.pdf
all: ${DOCUMENT}.pdf
# all: ${DOCUMENT}.ps
# all: ${DOCUMENT}.dvi
##
## 4) Use LaTeX or pdfLaTeX
LOGFILES = ${DOCUMENT}.log $(FILES:%=%.log)
AUXFILES = $(DOCUMENT).aux $(FILES:%=%.aux)
IDXFILES =  
##
## 4) Path and program specific configuration
## ==========================================
LATEX      = latex
PDFLATEX   = pdflatex
THUMBPDF   = thumbpdf 
BIBTEX     = bibtex  -min-crossrefs=99
BIBTOOL    = bibtool
MAKEINDEX  = makeindex
DVIPS      = dvips
EPS2PDF    = epstopdf
PS2PDF     = ps2pdf
GREP       = grep
EGREP      = egrep
FIG2DEV    = fig2dev 
THUMBPDF   = thumbpdf
RM         = rm
LN         = ln
MV   	   = mv	
SED        = sed
LATEX2HTML = latex2html
WWWBROWSER = netscape
#############################################################################
## No user configuration needed below this line                          ####
#############################################################################
##
## 7) Module selection
## ===================

include $(BASEDIR)/texmf/scripts/tex-makefile/include/netpbm.mk
include $(BASEDIR)/texmf/scripts/tex-makefile/include/pdflatex.mk
include $(BASEDIR)/texmf/scripts/tex-makefile/include/postscript.mk
include $(BASEDIR)/texmf/scripts/tex-makefile/include/graphivz.mk
include $(BASEDIR)/texmf/scripts/tex-makefile/include/mpost.mk
# include $(BASEDIR)/texmf/scripts/tex-makefile/include/magick.mk
include $(BASEDIR)/texmf/scripts/tex-makefile/include/check.mk
include $(BASEDIR)/texmf/scripts/tex-makefile/include/xfig.mk
include $(BASEDIR)/texmf/scripts/tex-makefile/include/dia.mk
#

##
## 6) Environment initialization and main rules
## ============================================
export TEXMFHOME

.PHONY = .clean .distclean
${DOCUMENT}.pdf: $(PIC)
${DOCUMENT}.ps:
${DOCUMENT}.dvi:
${DOCUMENT}_html:
${DOCUMENT}.idx: ${DOCUMENT}.tex $(SOURCES)
	$(LATEX) $<
${DOCUMENT}.ind: ${DOCUMENT}.idx
	$(MAKEINDEX) $(IDX_OPTIONS) $<
bibtex: 
	$(BIBTEX) ${DOCUMENT}
clean:
	$(RM) -f $(AUXFILES) $(LOGFILES)
	$(RM) -f $(IDXFILES)
	$(RM) -rf $(DOCUMENT) $(PIC)
	$(RM) -f *info *.tpt
	$(RM) -f *.idx *.lot *.ind *.ilg *.lof *.thm *.html *.toc *.out *.tmp  *.log *.bak *.aux *.bbl *.blg  *.eps *~
distclean: clean
	$(RM) -f *.pdf *.dvi *.ps 
