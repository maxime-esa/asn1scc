all:
	gnatmake -gnat2012 -d -P GPS_project.gpr mainprogram.adb --subdirs=debug -cargs -g -O0
	touch builtWithoutCoverage
	
coverage:
	if [ -f builtWithoutCoverage ] ; then make clean ; fi
	gnatmake -gnat2012 -d -P GPS_project.gpr mainprogram.adb --subdirs=debug -cargs -g -O0 -fprofile-arcs -ftest-coverage -largs -fprofile-arcs
	cd bin/debug ; ./mainprogram
	cd bin/debug ; gcov adaasn1rtl mod1
	
clean:
	rm -f builtWithoutCoverage ;
	gnat clean -r -P GPS_project.gpr --subdirs=debug	