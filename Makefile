# KNOWNTARGETS will not be passed along to CoqMakefile
KNOWNTARGETS := Makefile.coq extra-stuff extra-stuff2
# KNOWNFILES will not get implicit targets from the final rule, and so
# depending on them won't invoke the submake
# Warning: These files get declared as PHONY, so any targets depending
# on them always get rebuilt
KNOWNFILES   := Makefile _CoqProject

.PHONY: clean all coq verif 

.DEFAULT_GOAL := invoke-coqmakefile

invoke-coqmakefile: Makefile.coq
	$(MAKE) --no-print-directory -f Makefile.coq $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean:
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi 
	$(RM) Makefile.coq Makefile.coq.conf
	$(RM) C/sparse.v C/cholesky.v C/alloc.v C/densemat.v C/bandmat.v

INSTALLFILES1 ?= $(shell awk '/accuracy_proofs/{print $$NF"o"}' _CoqProject)

# INSTALLFILES2 ?= $(shell awk '/mathcomp_compat/{print $$NF"o"}' _CoqProject)

INSTALLDIR ?= $(shell realpath `coqc -where` | tr -d [:space:])/user-contrib/LAProof

install: build
	install -d $(INSTALLDIR)
	install -d $(INSTALLDIR)/accuracy_proofs
	install -d $(INSTALLDIR)/mathcomp_compat
	install -m 0644 $(INSTALLFILES1) $(INSTALLDIR)/accuracy_proofs
#	install -m 0644 $(INSTALLFILES2) $(INSTALLDIR)/mathcomp_compat

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
