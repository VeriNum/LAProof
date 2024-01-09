.PHONY: verif clean

verif: Makefile.coq
	$(MAKE) -f Makefile.coq

_CoqProject: _CoqProject.make
	cp _CoqProject.make _CoqProject

include ../common.mk

clean: clean-top
	rm -f _CoqProject
