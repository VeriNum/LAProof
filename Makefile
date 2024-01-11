.PHONY: clean all coq verif 

COQPATHFILE=$(wildcard _CoqPath)

build: coq

verif: _CoqProject.C
	cp _CoqProject.C _CoqProject 
	coq_makefile -f _CoqProject -o Makefile.coq
	$(MAKE) -f Makefile.coq

all: verif

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

clean-top: _CoqProject
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi 
	$(RM) Makefile.coq Makefile.coq.conf

clean: clean-top
	$(RM) _CoqProject	

_CoqProject: _CoqProject.acc
	cp _CoqProject.acc _CoqProject

INSTALLFILES1 ?= $(shell awk '/accuracy_proofs/{print $$NF"o"}' _CoqProject)

INSTALLFILES2 ?= $(shell awk '/mathcomp_compat/{print $$NF"o"}' _CoqProject)

INSTALLDIR ?= $(shell realpath `coqc -where` | tr -d [:space:])/user-contrib/LAProof

install: build
	install -d $(INSTALLDIR)
	install -d $(INSTALLDIR)/accuracy_proofs
	install -d $(INSTALLDIR)/mathcomp_compat
	install -m 0644 $(INSTALLFILES1) $(INSTALLDIR)/accuracy_proofs
	install -m 0644 $(INSTALLFILES2) $(INSTALLDIR)/mathcomp_compat

