# Shared make commands

.PHONY: coq clean-top 

coq: Makefile.coq
	$(MAKE) -f Makefile.coq

clean-top: _CoqProject
	if [ -e Makefile.coq ]; then $(MAKE) -f Makefile.coq cleanall; fi
	$(RM) Makefile.coq Makefile.coq.conf 

Makefile.coq: _CoqProject
	coq_makefile -f $< -o $@

