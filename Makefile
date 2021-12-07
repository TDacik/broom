.PHONY: build doc clean examples

build:
	dune build src/BroomTool.exe src/test.exe

doc: build
	dune build @doc
	[ -e doc ] || ln -sf _build/default/_doc/_html doc

examples:
	./scripts/run-examples

clean:
	rm -rf _build doc
