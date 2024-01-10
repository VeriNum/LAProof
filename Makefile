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

INSTALLFILES ?= $(shell make -Bn LAProof 2>/dev/null | awk '/^coqc.*v$$/{print $$NF"o"}')

# all the "realpath" complexity in the next line is to make it work on cygwin as well as regular unix
INSTALLDIR ?= $(shell realpath `coqc -where` | tr -d [:space:])/user-contrib/LAProof

install: build
	install -d $(INSTALLDIR)
	install -m 0644 $(INSTALLFILES) $(INSTALLDIR)


