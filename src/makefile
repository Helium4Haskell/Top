#-----------------------------------------------------------------------
# Constraint Solver
#-----------------------------------------------------------------------

# make example   - build an example executable
# make doc       - make haddock documentation 
# make clean	 - remove .hi and .o files and documentation
# make web       - make a distribution for the web (Bastiaan only)

default: example

prof:
	# build an example executable with profiling
	ghc -Wall --make -fglasgow-exts -prof -auto-all -o ../bin/csolver ../examples/Examples.hs

example:
	# build an example executable
	ghc -Wall --make -fglasgow-exts -o ../bin/csolver ../examples/Examples.hs
        
documentation:
	# make haddock documentation        
	haddock -html -o ../doc \
          Top/*.hs \
	  Top/*/*.hs \
          
clean:
	#remove .hi and .o files and documentation
	$(RM) `find . -name "*.o" -print`
	$(RM) `find . -name "*.hi" -print`
	$(RM) ../doc/*.html
	$(RM) ../doc/*.css
	$(RM) ../doc/*.gif                
	$(RM) ../bin/csolver

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
