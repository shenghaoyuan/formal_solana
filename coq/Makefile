include Makefile.config

COQC := coqc
COQMAKEFILE := coq_makefile


THIS_FILE := $(lastword $(MAKEFILE_LIST))

COQEXTRAFLAGS := COQEXTRAFLAGS = '-w all,-extraction,-disj-pattern-notation'

DIRS := comm model

COQINCLUDES := INSTALLDEFAULTROOT = comm "\n"
COQINCLUDES += $(foreach d, $(DIRS),-R $(d) bpf.$(d) "\n")
COQINCLUDES +=-R $(COMPCERTDIR) compcert

COQDEP="$(COQBIN)coqdep" -exclude-dir aarch64 -exclude-dir x86_64 -exclude-dir riscV -exclude-dir powerpc -exclude-dir x86_32 $(COQINCLUDES)

all:
	@echo $@
	@$(MAKE) comm
	@$(MAKE) model
   
COMM= rBPFCommType.v rBPFSyntax.v vm.v vm_state.v ebpf.v rBPFDecoder.v
# Interpreter.v
   
# MODEL= Syntax.v Decode.v Semantics.v

COQCOMM = $(addprefix comm/, $(COMM))
COQMODEL =  $(addprefix model/, $(MODEL))

FILES= $(COQCOMM) $(COQMODEL)

depend: $(FILES)
	@echo "Analyzing Coq dependencies"
	@$(COQDEP) $^ > .depend

comm:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQCOMM) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

model:
	@echo $@
	$(COQMAKEFILE) -f _CoqProject $(COQMODEL) $(COQEXTRAFLAGS)  -o CoqMakefile
	make -f CoqMakefile

CoqProject:
	@echo $(COQINCLUDES) > _CoqProject

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

.PHONY: all comm model CoqProject clean
