fancy introduction...

## Building from sources


### Ocaml dependences
     - atd
     - core
     - cppo
     - dune
     - ppx_compare, ppx_deriving
     - qtest
     - z3 <= 3.4.8.1

For JSON dumper see [code-listener/README](https://github.com/versokova/predator/blob/json/README)

```
opam install atd core cppo z3 dune qtest
eval `opam config env`

./build.sh           # for custom installation of gcc, set $GCC_HOST
dune build src/biabductor.exe src/ContractGenerator.exe src/test.exe
```

### Troubleshooting

* For `atd 2.0+`: the module AGU must be set correctly in these files:
  ```
  gsed -i 's/Ag_util/Atdgen_runtime.Util/' code-listener/json/Check.ml src/CL/Util.ml
  ```

* Z3 Installation failed on MacOS with `clang: error: unsupported option '-fopenmp'`:
  a newer compiler must be used (e.g. `brew install llvm` and set `$CC` and `$CXX` to a newer clang).

* If scripts doesn't work due to Z3, set the search path for shared libraries
  ```
  export LD_LIBRARY_PATH=`opam config var z3:lib`
  export DYLD_LIBRARY_PATH=`opam config var z3:lib` # for OSX
  ```

To run the tests:
```
dune runtest
```
## Usage
```
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
