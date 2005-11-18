#-----------------------------------------------------------------------
# Constraint Solver
#-----------------------------------------------------------------------

# make example   - build the Top constraint solver
# make doc       - make haddock documentation 
# make clean	 - remove .hi and .o files and documentation

default: all

all : topsolver topsolver

prof:
	# build the Top constraint solver with profiling
	ghc -Wall --make -package text -fglasgow-exts -prof -auto-all -o ../bin/topsolver TopSolver.hs

topsolver:
	# build the Top constraint solver
	ghc -Wall --make -package text -fglasgow-exts -o ../bin/topsolver TopSolver.hs
        
doc:
	# make haddock documentation        
	haddock --title=Top --prologue=prologue --html -o ../doc \
          Top/*.hs \
	  Top/*/*.hs \
          
ignore :
	svn propset -R svn:ignore -F ../svn-ignore ..

clean:
	#remove .hi and .o files and documentation
	$(RM) `find . -name "*.o" -print`
	$(RM) `find . -name "*.hi" -print`
	$(RM) ../doc/*.html
	$(RM) ../doc/*.css
	$(RM) ../doc/*.gif                
	$(RM) ../bin/topsolver


#-----------------------------------------------------------------------
# Cobalt
#-----------------------------------------------------------------------

.SUFFIXES : .o .hs .hi .lhs .hc	.s .ag

AG = ag

# AG sources
AGSOURCES = \
     Top/Cobalt/AGSyntax.hs Top/Cobalt/Syntax.hs Top/Cobalt/Generator.hs

Top/Cobalt/AGSyntax.hs : \
	Top/Cobalt/AGSyntax.ag
	#ag AGSyntax
	cd Top/Cobalt; $(AG) -dm --module=Top.Cobalt.AGSyntax AGSyntax.ag; cd ../..

Top/Cobalt/Syntax.hs : \
	Top/Cobalt/Syntax.ag
	Top/Cobalt/AGSyntax.hs Top/Cobalt/ShowAG.hs
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

ag : $(AGSOURCES)