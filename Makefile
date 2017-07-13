include compcert/Makefile.config

COQINC = -R $(ARCH) "" -R compcert compcert

OCAMLBUILD = ocamlbuild -lib str
OCAMLINC   = \
	-I vcodegen -I compcert/extraction \
	-I compcert/lib -I compcert/common -I compcert/driver \
	-I compcert/backend -I compcert/cfrontend -I compcert/cparser \
	-I compcert/$(ARCH)/$(VARIANT) -I compcert/$(ARCH)

FILES = \
	Violaconf.v \
	Violaspec.v \
	Violatrans.v \
	Violaall.v \
	Violadevspecs.v
	
all:    vtests/test_genasm.native

vtests/test_%.native: vtests/test_%.ml vcodegen/extraction.vo
	rm -f $@
	$(OCAMLBUILD) $(OCAMLINC) -no-links $@
	ln -s $(CURDIR)/_build/$@ $@

vcodegen/extraction.vo: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: Makefile $(FILES) $(PROOFFILES)
	coq_makefile -install none $(COQINC) $(FILES) $(PROOFFILES) -o $@

Arch.v: Makefile
	@echo "Require Export compcert.$(ARCH).Asm." > $@
	@echo "Require Export compcert.$(ARCH).Asmgen." >> $@

.PRECIOUS: vtests/test_%.native

clean:
	rm -rf _build *.vo *.glob *.d vtests/*.native
	cd vcodegen && rm -f *.ml *.mli *.mlo *.glob *.vo
	rm -f Arch.v
