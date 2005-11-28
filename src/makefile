#-----------------------------------------------------------------------
# Top Library
#-----------------------------------------------------------------------

.PHONY:  clean cobalt

default: all
all: topsolver cobalt

#-----------------------------------------------------------------------
# Compilers and Tools
#-----------------------------------------------------------------------

AG = ag
HC = ghc
HADDOCK = haddock

HC_OPTS = -static -fglasgow-exts -Wall

DOC_DIR = ../doc
BIN_DIR = ../bin

#-----------------------------------------------------------------------
# General targets
#-----------------------------------------------------------------------

doc:
	# make haddock documentation        
	$(HADDOCK) --title=Top --prologue=prologue --html -o $(DOC_DIR) Top/*.hs Top/*/*.hs

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

#-----------------------------------------------------------------------
# Cobalt
#-----------------------------------------------------------------------

# Cobalt's AG sources
COBALT_AG = \
     Top/Cobalt/AGSyntax.hs Top/Cobalt/Syntax.hs Top/Cobalt/Generator.hs

Top/Cobalt/AGSyntax.hs : \
	Top/Cobalt/AGSyntax.ag

	#ag AGSyntax
	cd Top/Cobalt; $(AG) -dm --module=Top.Cobalt.AGSyntax AGSyntax.ag; cd ../..

Top/Cobalt/Syntax.hs : \
	Top/Cobalt/Syntax.ag Top/Cobalt/AGSyntax.hs Top/Cobalt/ShowAG.hs

	#ag Syntax
	cd Top/Cobalt; $(AG) -dm --module=Top.Cobalt.Syntax Syntax.ag; cd ../..

Top/Cobalt/Generator.hs : \
	Top/Cobalt/Generator.ag \
	Top/Cobalt/AGSyntax.ag Top/Cobalt/Syntax.ag Top/Cobalt/Analyze.ag \
	Top/Cobalt/InferTypes.ag Top/Cobalt/CodeGen.ag Top/Cobalt/Escape.hs \
	Top/Cobalt/ParseRules.hs Top/Cobalt/ShowAG.hs Top/Cobalt/AGSyntax.hs \
	Top/Cobalt/Syntax.hs Top/Types.hs

	#ag Generator
	cd Top/Cobalt; $(AG) -cfs --self --module=Top.Cobalt.Generator Generator.ag; cd ../..

cobalt: $(COBALT_AG)

ag : $(COBALT_AG)