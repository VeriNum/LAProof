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



