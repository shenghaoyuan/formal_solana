solve:
	sed -i 's/type int = int//g' step_test.ml
	sed -i 's/type int = int//g' step_test.mli
#	sed -i 's/type int = int//g' interpreter_test.ml
#	sed -i 's/type int = int//g' interpreter_test.mli

compile:
	make clean
	ocamlc -c step_test.ml
#	ocamlc -c step_test2.ml
	ocamlfind ocamlc -o step_test -linkpkg step_test.cmo example.ml
#	ocamlfind ocamlc -o step2 -package yojson -linkpkg step_test2.cmo step2.ml


clean:
	@echo $@
	find . -name "step_test" -exec rm {} \;
	find . -name "step_test2" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmo" -exec rm {} \;
	find . -name "*\.cmx" -exec rm {} \;
	
	
run:
	@echo "run example"
	./example
	@echo "/n/nrun step2"
	./step2


.PHONY: compile clean run solve

