looper:
	@-echo -e "Compiling Coq file makeLooper.v..."
	coqc -R ../../ Top makeLooper.v > errorInMakefile.txt 2>&1
	runhaskell looper.hs > looper.c
	iverilog looper.c -o looper 
	@-$(MAKE) cleanTemp > errorInMakefile.txt 2>&1 || true
	@-echo -e "Verilog file looper.c\nCompiled looper.c to executable looper..."

rotate:
	@-echo -e "Compiling Coq file testRightRotate.v..."
	coqc -R ../../ Top testRightRotate.v > errorInMakefile.txt 2>&1
	runhaskell rotate.hs > rotate.c
	iverilog rotate.c -o rotate 
	@-$(MAKE) cleanTemp > errorInMakefile.txt 2>&1 || true
	@-echo -e "Verilog file rotate.c\nCompiled rotate.c to executable rotate..."

tests: 
	$(MAKE) rotate 2> errorInMakefile.txt || true
	$(MAKE) looper 2> errorInMakefile.txt || true



cleanTemp:
	@-rm *.hs > errorInMakefile.txt 2>&1 || true
	@-rm *.vo > errorInMakefile.txt 2>&1 || true
	@-rm *.glob > errorInMakefile.txt 2>&1 || true
	@-rm *~ > errorInMakefile.txt 2>&1 || true


clean:
	@-rm rotate 2> /dev/null || true
	@-rm looper 2> /dev/null || true
	@-rm sha256 2> /dev/null || true
	@-rm sha256_32 2> /dev/null || true
	@-rm sha256_24 2> /dev/null || true
	@-rm hmac 2> /dev/null || true
	@-rm *.c 2> /dev/null || true
	@-rm *.hs 2> /dev/null || true
	@-rm *.vo 2> /dev/null || true
	@-rm *.glob 2> /dev/null || true
	@-rm *~ 2> /dev/null || true
	@- rm errorInMakefile.txt 2> /dev/null || true

