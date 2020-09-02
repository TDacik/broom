fancy introduction...

## Building from sources

1) Install opam (minimal version 2.0.0) and libyojson-ocaml-dev (we need ydump)

   ```
   sudo apt install opam                    ### for Ubuntu
   sudo apt install libyojson-ocaml-dev
   ```

2) Install dependencies by opam:
   ```
   opam install atdgen core cppo dune ppx_compare ppx_deriving qtest z3
   ```
3) Do some setup (TODO: explain why)
   ```
   export COMPILER="ocaml-variants.4.09.1+flambda"
   export SWITCH=$COMPILER
   opam init
   opam switch create $SWITCH $COMPILER  
   eval `opam config env`
   opam update
   ```
4) Install bi-abductor etc.:
   ```
   git clone --recurse-submodules https://pajda.fit.vutbr.cz/rogalew/bi-work.git
   cd bi-work       ### continue in this directory
   opam install --deps-only bi .
   ./build.sh
   dune build src/biabductor.exe src/ContractGenerator.exe src/test.exe
   ```

5) Simple test:
   ```
   ./scripts/json_dumper  tests/easy-01-ok.c | ./scripts/generator
   ./scripts/biabductor   tests/easy-01-ok.c
   ```
 

 

### List of dependencies
     - opam             >= 2.0.0,  (Ubuntu: "sudo apt install opam")
     next install by "opam install  atdgen core cppo dune ppx_compare ppx_deriving qtest z3"
     - atdgen
     - core
     - cppo
     - dune
     - ppx_compare, ppx_deriving
     - qtest
     - z3              = 4.8.8-1

For JSON dumper see [code-listener/README](https://github.com/versokova/predator/blob/json/README)

### Install dependencies
```
brew install opam                                        # for MacOS
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
* `ld: warning: directory not found for option '-L/opt/local/lib'` appears
  during compilation on MacOS. The cause is `zarith` (dependence from Z3).
  To suppress the message, create the `/opt/local/lib` folder.

* Z3 Installation failed on MacOS with `clang: error: unsupported option '-fopenmp'`:
  Z3 <=4.8.1 requires a compiler with OpenMP support. The minimum required
  version of Z3 is 4.8.8-1.

* If scripts doesn't work due to Z3, set the search path for shared libraries
  ```
  export LD_LIBRARY_PATH=`opam config var z3:lib`
  export DYLD_LIBRARY_PATH=`opam config var z3:lib`      # for MacOS
  ```
  Version Z3 4.8.8-1 uses static libraries. This stap indicates that you use an old version.

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
