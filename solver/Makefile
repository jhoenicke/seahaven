
../static/solver.js: solver.c Makefile
	emcc solver.c -O3 -s WASM=1 --closure 1 --memory-init-file 0 -s ENVIRONMENT=worker -s  FILESYSTEM=0 -s EXPORTED_FUNCTIONS="['_initcard','_solve']" -s BUILD_AS_WORKER=1 -o ../static/solver.js
