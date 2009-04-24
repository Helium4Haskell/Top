#-----------------------------------------------------------------------
# Top Library
#-----------------------------------------------------------------------

.PHONY:  clean

default: topsolver
all: topsolver 

#-----------------------------------------------------------------------
# Compilers and Tools
#-----------------------------------------------------------------------

AG = uuagc
# AG = /Volumes/Apps/uuagc-visage/dist/build/src/uuagc
HC = ghc
HADDOCK = haddock

HC_OPTS = -Wall

DOC_DIR = ../doc
BIN_DIR = ../bin

#-----------------------------------------------------------------------
# General targets
#-----------------------------------------------------------------------

doc:
	# make haddock documentation        
	$(HADDOCK) --title="The Top Library" --prologue=$(DOC_DIR)/prologue --html -o $(DOC_DIR) \
	   Top/*.hs Top/*/*.hs Top/*/*/*.hs

ignore:
	svn propset -R svn:ignore -F ../svn-ignore ..

clean:
	#remove .hi and .o files and documentation
	$(RM) `find . -name "*.o" -print`
	$(RM) `find . -name "*.hi" -print`
	$(RM) $(DOC_DIR)/*.html
	$(RM) $(DOC_DIR)/*.css
	$(RM) $(DOC_DIR)/*.gif                
	$(RM) $(BIN_DIR)/topsolver

#-----------------------------------------------------------------------
# Constraint Solver
#-----------------------------------------------------------------------

topsolver:
	# build the Top constraint solver
	$(HC) $(HC_OPTS) --make -o $(BIN_DIR)/topsolver TopSolver.hs

topsolver-prof:
	# build the Top constraint solver with profiling
	$(HC) $(HC_OPTS) --make -package text -prof -auto-all -o $(BIN_DIR)/topsolver TopSolver.hs

