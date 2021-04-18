
solver.js: solver.c
	emcc solver.c -s WASM=0 -s EXPORTED_FUNCTIONS="['_initcard','_solve']" -s BUILD_AS_WORKER=1 -o solver.js
