all:
	$(MAKE) hmac 2> errorInMakefile.txt || true
#	$(MAKE) sha256basic 2> errorInMakefile.txt || true
	$(MAKE) sha256 2> errorInMakefile.txt || true

hmac: ../hmac.v
	cd .. && $(MAKE); cd Extraction
	@-echo -e "Compiling Coq makeHmac.v..."
	coqc -R ../ Top makeHmac.v > errorInMakefile.txt 2>&1
	runhaskell hmac.hs > hmac.sv
	iverilog hmac.sv -o hmac 
	@-$(MAKE) cleanTemp > errorInMakefile.txt 2>&1 || true
	@-echo -e "Verilog file hmac.sv\nCompiled hmac.sv to executable hmac..."

sha256basic: ../sha256.v
	cd .. && $(MAKE); cd Extraction
	@-echo -e "Compiling Coq file makeSha256basic.v..."
	coqc -R ../ Top makeSha256basic.v > errorInMakefile.txt 2>&1
	runhaskell sha256.hs > sha256.sv
	iverilog sha256.sv -o sha256 
	@-$(MAKE) cleanTemp > errorInMakefile.txt 2>&1 || true
	@-echo -e "Verilog file sha256.sv\nCompiled sha256.sv to executable sha256..."

sha256: ../sha256.v
	cd .. && $(MAKE); cd Extraction
	@-echo -e "Compiling Coq file makeSha256.v..."
	coqc -R ../ Top makeSha256.v > errorInMakefile.txt 2>&1
	runhaskell sha256_32.hs > sha256_32.sv
	runhaskell sha256_24.hs > sha256_24.sv
	iverilog sha256_32.sv -o sha256_32
	iverilog sha256_24.sv -o sha256_24	
	@-$(MAKE) cleanTemp > errorInMakefile.txt 2>&1 || true
	@-echo -e "Verilog file sha256.sv\nCompiled sha256_(32|24).sv to executable sha256_(32|24)..."


looper:
	cd .. && $(MAKE); cd Extraction
	@-echo -e "Compiling Coq file makeLooper.v..."
	coqc -R ../ Top makeLooper.v > errorInMakefile.txt 2>&1
	runhaskell looper.hs > looper.sv
	iverilog looper.sv -o looper 
	@-$(MAKE) cleanTemp > errorInMakefile.txt 2>&1 || true
	@-echo -e "Verilog file looper.sv\nCompiled looper.sv to executable looper..."

test1:
	cd .. && $(MAKE); cd Extraction
	@-echo -e "Compiling Coq file testRightRotate.v..."
	coqc -R ../ Top testRightRotate.v > errorInMakefile.txt 2>&1
	runhaskell rotate.hs > rotate.sv
	iverilog rotate.sv -o rotate 
	@-$(MAKE) cleanTemp > errorInMakefile.txt 2>&1 || true
	@-echo -e "Verilog file rotate.sv\nCompiled rotate.sv to executable rotate..."


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
	@-rm *.sv 2> /dev/null || true
	@-rm *.hs 2> /dev/null || true
	@-rm *.vo 2> /dev/null || true
	@-rm *.glob 2> /dev/null || true
	@-rm *~ 2> /dev/null || true
	@- rm errorInMakefile.txt 2> /dev/null || true

