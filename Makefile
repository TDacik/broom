.PHONY: build doc clean

build:
	dune build src/biabductor.exe src/ContractGenerator.exe src/test.exe

doc: build
	dune build @doc
	[ -e doc ] || ln -sf _build/default/_doc/_html doc

clean:
	rm -rf _build doc