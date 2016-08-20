IDRIS := idris
LIB   := resources
OPTS  :=

.PHONY: doc test clobber check clean lib install

install: lib
	${IDRIS} ${OPTS} --install ${LIB}.ipkg

lib:
	${IDRIS} ${OPTS} --build ${LIB}.ipkg

clean:
	${IDRIS} --clean ${LIB}.ipkg
	find . -name "*~" -delete

check: clobber
	${IDRIS} --checkpkg ${LIB}.ipkg

clobber : clean
	find . \(   -name "*.ibc" \
			-or -name "*~"    \
			-or -name "*.o"   \
			\) -delete


doc:
	${IDRIS} --mkdoc ${LIB}.ipkg
