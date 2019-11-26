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
export LD_LIBRARY_PATH=`opam config var z3:lib`
dune build
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

## See also
   * [atd's documentation](http://atd.readthedocs.io/en/latest/)
   * [yojson's documentation](https://docs.mirage.io/yojson/Yojson/index.html)

## Contact
For more information send an e-mail to:

* Petr Peringer <peringer@fit.vutbr.cz> (corresponding author of JSON dumper)
* etc.
