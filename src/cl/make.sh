#!/bin/bash

# don't use !!!

ocamlfind ocamlc -c Loc.mli -package atdgen
ocamlfind ocamlc -c Loc.ml -package atdgen
ocamlfind ocamlc -c Type.mli -package atdgen
ocamlfind ocamlc -c Type.ml -package atdgen
ocamlfind ocamlc -c Operand.mli -package atdgen
ocamlfind ocamlc -c Operand.ml -package atdgen
ocamlfind ocamlc -c Fnc.mli -package atdgen
ocamlfind ocamlc -c Fnc.ml -package atdgen
ocamlfind ocamlc -c Var.mli -package atdgen
ocamlfind ocamlc -c Var.ml -package atdgen
ocamlfind ocamlc -c Storage.mli -package atdgen
ocamlfind ocamlc -c Storage.ml -package atdgen

ocamlfind ocamlc -c Util.mli -package atdgen
ocamlfind ocamlc -c Util.ml -package atdgen
cppo Printer.ml -o Printer.cppo.ml
ocamlfind ocamlc -c Printer.mli -package atdgen
ocamlfind ocamlc -c Printer.cppo.ml -package atdgen
ocamlfind ocamlc -c ../ContractGenerator.ml -package atdgen -o ../ContractGenerator
ocamlfind ocamlc -o generator Loc.cmo Type.cmo Operand.cmo Fnc.cmo Var.cmo Storage.cmo Util.cmo Printer.cppo.cmo ../ContractGenerator.cmo -package atdgen  -linkpkg

exit
