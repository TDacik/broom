fancy introduction...

## Building from sources


### Ocaml dependences
     - atd
     - core
     - cppo
     - dune
     - ppx_compare, ppx_deriving
     - qtest
     - z3

For JSON dumper see [code-listener/README](https://github.com/versokova/predator/blob/json/README)

```
./build.sh      # for custom installation of gcc, set $GCC_HOST

opam install atd core cppo z3 dune qtest
eval `opam config env`
dune build src/biabductor.exe src/ContractGenerator.exe
```

### Troubleshooting

* For `atd 2.0+`: the module AGU must be set correctly  in the files `code-listener/json/Check.ml`, `src/CL/Util.ml`

* If Z3 doesn't work: set the search path for shared libraries
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
./scripts/json_dumper file.c | ./scripts/generator
./scripts/biabductor
```
Scripts `generator` and `biabductor` expect input due to the CL library. **[Need to be fixed!]**

## Attention
Need to be fixed!
 * the module AGU must be set correctly  in the files `code-listener/json/Check.ml`, `src/CL/Util.ml`
 * scripts expect input due to the CL library

## See also
   * [atd's documentation](http://atd.readthedocs.io/en/latest/)
   * [yojson's documentation](https://docs.mirage.io/yojson/Yojson/index.html)

## Contact
For more information send an e-mail to:

* Petr Peringer <peringer@fit.vutbr.cz> (corresponding author of JSON dumper)
* etc.
