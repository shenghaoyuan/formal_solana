include Makefile.config

COQC := coqc
COQMAKEFILE := coq_makefile


THIS_FILE := $(lastword $(MAKEFILE_LIST))

COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

DIRS := model

COQINCLUDES := INSTALLDEFAULTROOT = model "\n"
COQINCLUDES += $(foreach d, $(DIRS),-R $(d) bpf.$(d) "\n")
COQINCLUDES +=-R $(COMPCERTDIR) compcert

COQDEP="$(COQBIN)coqdep" -exclude-dir aarch64 -exclude-dir x86_64 -exclude-dir riscV -exclude-dir powerpc -exclude-dir x86_32 $(COQINCLUDES)

all:
	@echo $@
	@$(MAKE) model
   
MODEL= rBPFCommType.v rBPFSyntax.v vm.v vm_state.v ebpf.v rBPFDecoder.v Interpreter.v rBPFEncoder.v BitfieldLemma.v BinSolver.v MyTactic.v Consistency1.v Consistency2.v 

COQMODEL =  $(addprefix model/, $(MODEL))

FILES= $(COQMODEL)

depend: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

model:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQMODEL) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

micro-test:
	@cd ../test/exec_semantics/coq_test && \
	eval $$(opam env) && \
	ocamlc -c step_test.ml && \
	ocamlfind ocamlc -o step -package yojson -linkpkg step_test.cmo step.ml && \
	./step

macro-test:
	@cd ../test/exec_semantics/coq_test && \
	ocamlc -c interpreter_test.ml && \
	ocamlc -o test interpreter_test.cmo test.ml && \
	./test

clean :
	@echo $@
	make -f CoqMakefile clean
	find . -name "*\.vo" -exec rm {} \;
	find . -name "*\.vok" -exec rm {} \;
	find . -name "*\.vos" -exec rm {} \;
	find . -name "*\.glob" -exec rm {} \;
	find . -name "*\.aux" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;
	find . -name "*\.crashcoqide" -exec rm {} \;

.SECONDARY:

.PHONY: all model CoqProject clean micro-test macro-test
