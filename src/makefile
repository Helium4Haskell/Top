#-----------------------------------------------------------------------
# Constraint Solver
#-----------------------------------------------------------------------

# make example   - build the Top constraint solver
# make doc       - make haddock documentation 
# make clean	 - remove .hi and .o files and documentation

default: topsolver

prof:
	# build the Top constraint solver with profiling
	ghc -Wall --make -package text -fglasgow-exts -prof -auto-all -o ../bin/topsolver TopSolver.hs

topsolver:
	# build the Top constraint solver
	ghc -Wall --make -package text -fglasgow-exts -o ../bin/topsolver TopSolver.hs
        
documentation:
	# make haddock documentation        
	haddock --title=Top --prologue=prologue -html -o ../doc \
          Top/*.hs \
	  Top/*/*.hs \
          
clean:
	#remove .hi and .o files and documentation
	$(RM) `find . -name "*.o" -print`
	$(RM) `find . -name "*.hi" -print`
	$(RM) ../doc/*.html
	$(RM) ../doc/*.css
	$(RM) ../doc/*.gif                
	$(RM) ../bin/topsolver
