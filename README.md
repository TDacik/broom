fancy introduction...

## Building from sources


### List of dependencies
     - opam             >= 2.0.0
     - atdgen
     - core
     - cppo
     - dune
     - ppx_compare, ppx_deriving
     - qtest
     - z3                = 4.8.1

For JSON dumper see [code-listener/README](https://github.com/versokova/predator/blob/json/README)

### Install dependencies
```
bew install opam                                         # for MacOS
```
```
$COMPILER="ocaml-variants.4.09.1+flambda"
$SWITCH=$COMPILER

opam init
opam switch create $SWITCH $COMPILER
eval `opam config env`
opam update
opam install --deps-only bi .
```

### Build
```
./build.sh           # for custom installation of gcc, set $GCC_HOST
dune build src/biabductor.exe src/ContractGenerator.exe src/test.exe
```

### Troubleshooting

* Empty the `code-listener` directory:
  ```
  git clone --recurse-submodules https://pajda.fit.vutbr.cz/rogalew/bi-work.git
  ```

* Z3 Installation failed on MacOS with `clang: error: unsupported option '-fopenmp'`:
  a newer compiler must be used (e.g. `brew install llvm` and set `$CC` and `$CXX` to a newer clang).

* If scripts doesn't work due to Z3, set the search path for shared libraries
  ```
  export LD_LIBRARY_PATH=`opam config var z3:lib`
  export DYLD_LIBRARY_PATH=`opam config var z3:lib`      # for MacOS
  ```

To run the tests:
```
dune runtest
```
## Usage
```
./scripts/call_graph file.c            # create DOTs (call graph, CFGs) from C
./scripts/json_dumper [-m32] file.c > file.json           # create JSON from C
./scripts/generator < file.json                           # print contracts
./scripts/json_dumper file.c | ./scripts/generator
./scripts/biabductor [-m32] file.c                        # main binary
./scripts/test
```
CL library expects input in json-format. **[Need to be fixed!]**

## See also
   * [atd's documentation](http://atd.readthedocs.io/en/latest/)
   * [yojson's documentation](https://docs.mirage.io/yojson/Yojson/index.html)

## Contact
For more information send an e-mail to:

* Petr Peringer <peringer@fit.vutbr.cz> (corresponding author of JSON dumper)
* etc.
