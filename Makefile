KNOWNTARGETS := CoqMakefile
KNOWNFILES   := Makefile _CoqProject

.DEFAULT_GOAL := invoke-coqmakefile

CoqMakefile: Makefile _CoqProject
	$(COQBIN)coq_makefile -docroot LAProof -f _CoqProject -o CoqMakefile

invoke-coqmakefile: CoqMakefile
	$(echo hello)
	$(MAKE) --no-print-directory -f CoqMakefile $(filter-out $(KNOWNTARGETS),$(MAKECMDGOALS))

.PHONY: invoke-coqmakefile $(KNOWNFILES)

clean:
	if [ -e CoqMakefile ]; then $(MAKE) -f CoqMakefile cleanall; fi
	$(RM) $(wildcard CoqMakefile CoqMakefile.conf) 

# This should be the last rule, to handle any targets not declared above
%: invoke-coqmakefile
	@true
