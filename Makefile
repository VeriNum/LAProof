.PHONY: clean all coq verif

COQPATHFILE=$(wildcard _CoqPath)

build: coq

include common.mk

all:
	$(MAKE) coq
	$(MAKE) C

verif:
	$(MAKE) -C C

clean: clean-top
	$(RM) _CoqProject	
	$(MAKE) -C C clean

_CoqProject: _CoqProject.make
	cp _CoqProject.make _CoqProject

INSTALLFILES1 ?= $(shell awk '/accuracy_proofs/{print $$NF"o"}' _CoqProject)

INSTALLFILES2 ?= $(shell awk '/mathcomp_compat/{print $$NF"o"}' _CoqProject)

INSTALLDIR ?= $(shell realpath `coqc -where` | tr -d [:space:])/user-contrib/LAProof

install: build
	install -d $(INSTALLDIR)
	install -d $(INSTALLDIR)/accuracy_proofs
	install -d $(INSTALLDIR)/mathcomp_compat
	install -m 0644 $(INSTALLFILES1) $(INSTALLDIR)/accuracy_proofs
	install -m 0644 $(INSTALLFILES2) $(INSTALLDIR)/mathcomp_compat

