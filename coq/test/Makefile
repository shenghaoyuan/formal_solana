solve:
	find . -name "step_test.mli" -exec rm {} \;
	find . -name "interpreter_test.mli" -exec rm {} \;

stepcomp:
	ocamlc -c step_test.ml
	ocamlfind ocamlc -o step -package yojson -linkpkg step_test.cmo step.ml

interpretercomp:
	ocamlc -c interpreter_test.ml
	ocamlfind ocamlc -o test -package yojson -linkpkg interpreter_test.cmo test.ml

trans:
	ocamlfind ocamlc -o solve -package yojson -linkpkg solve.ml
	./solve
	find . -name "solve" -exec rm {} \;
	find . -name "solve.cmi" -exec rm {} \;
	find . -name "solve.cmo" -exec rm {} \;

clean:
	@echo $@
	find . -name "step" -exec rm {} \;
	find . -name "test" -exec rm {} \;
	find . -name "*\.cmi" -exec rm {} \;
	find . -name "*\.cmo" -exec rm {} \;
	
step:
	@echo "run step"
	./step

interpreter:
	@echo "run test"
	./test

.PHONY: stepcomp interpretercomp clean step interpreter solve interpretertest steptest trans testtemp $(opam env)

