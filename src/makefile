#-----------------------------------------------------------------------
# Constraint Solver
#-----------------------------------------------------------------------

# make examp le   - build the Top constraint solver
# make doc       - make haddock documentation 
# make clean	 - remove .hi and .o files and documentation
# make web       - make a distribution for the web (Bastiaan only)

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

web:
	#*** Bastiaan only ***
	#make a distribution for the web
	$(RM) /import/sherlock/www/people/bastiaan/top.zip
	make clean
	make documentation
	zip top -r ../*
	mv top.zip /import/sherlock/www/people/bastiaan
	chmod 744 /import/sherlock/www/people/bastiaan/top.zip
	ls -l /import/sherlock/www/people/bastiaan/top.zip
	#*************************************************
	# top.zip is moved to the Homepage
	#*************************************************
