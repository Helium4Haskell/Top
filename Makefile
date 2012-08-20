#-----------------------------------------------------------------------
# Top Library
#-----------------------------------------------------------------------

.PHONY:  clean doc report

default: topsolver
all: topsolver doc report

#-----------------------------------------------------------------------
# Compilers and Tools
#-----------------------------------------------------------------------

HC      = ghc
HADDOCK = haddock
HLINT   = hlint

HC_OPTS = -Wall -i$(SRCDIR) -odir $(OUTDIR) -hidir $(OUTDIR)

SRCDIR = src
BINDIR = bin
OUTDIR = out
DOCDIR = doc

RM = rm -rf

HSFILES = $(wildcard $(SRCDIR)/*.hs $(SRCDIR)/*/*.hs $(SRCDIR)/*/*/*.hs $(SRCDIR)/*/*/*/*.hs)

#-----------------------------------------------------------------------
# General targets
#-----------------------------------------------------------------------

doc:
	# make haddock documentation        
	$(HADDOCK) --title="The Top Library" --prologue=$(DOCDIR)/prologue --html -o $(DOCDIR) \
	   $(HSFILES)

clean:
	#remove .hi and .o files and documentation
	$(RM) $(OUTDIR)
	$(RM) $(BINDIR)/*
	$(RM) $(DOCDIR)/*.html
	$(RM) $(DOCDIR)/*.css
	$(RM) $(DOCDIR)/*.gif
	$(RM) $(DOCDIR)/*.js
	$(RM) $(DOCDIR)/*.png
	$(RM) $(SRCDIR)/*.o
	$(RM) $(SRCDIR)/*/*.o
	$(RM) $(SRCDIR)/*/*/*.o
	$(RM) $(SRCDIR)/*/*/*/*.o
	$(RM) $(SRCDIR)/*.hi
	$(RM) $(SRCDIR)/*/*.hi
	$(RM) $(SRCDIR)/*/*/*.hi
	$(RM) $(SRCDIR)/*/*/*/*.hi

report:
	$(HLINT) --report=$(DOCDIR)/report.html .

#-----------------------------------------------------------------------
# Constraint Solver
#-----------------------------------------------------------------------

topsolver:
	# build the Top constraint solver
	$(HC) $(HC_OPTS) --make -o $(BINDIR)/topsolver $(SRCDIR)/TopSolver.hs
