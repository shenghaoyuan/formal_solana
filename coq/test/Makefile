solve:
	rm step_test.mli
	rm interpreter_test.mli

compile:
	ocamlc -c step_test.ml
	ocamlc -c step_test2.ml
	ocamlfind ocamlc -o step -package yojson -linkpkg step_test.cmo step.ml
	ocamlfind ocamlc -o step2 -package yojson -linkpkg step_test2.cmo step2.ml

trans:
	ocamlfind ocamlc -o solve -package yojson -linkpkg solve.ml
	./solve
	find . -name "solve" -exec rm {} \;
	find . -name "solve.cmi" -exec rm {} \;
	find . -name "solve.cmo" -exec rm {} \;

clean:
	@echo $@
	find . -name "step" -exec rm {} \;
	find . -name "step2" -exec rm {} \;
	find . -name "solve" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmo" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;

test:
	ocamlc -c step_test1.ml
	ocamlfind ocamlc -o step1 -package yojson -linkpkg step_test1.cmo step1.ml
	./step1
	find . -name "step1" -exec rm {} \;
	find . -name "step_test1.cmi" -exec rm {} \;
	find . -name "step_test1.cmo" -exec rm {} \;
	
run:
	@echo "run step"
	./step
	@echo "\nrun step2"
	./step2


.PHONY: compile clean run solve test trans

