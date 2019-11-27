fancy introduction...

## Building from sources

For JSON dumper see [code-listener/README](https://github.com/versokova/predator/blob/json/README)

```
./build.sh      # for custom installation of gcc, set $GCC_HOST
dune build
```

### Ocaml dependences
     - atd
     - cppo
     - dune
     - ppx_compare, ppx_deriving
     - z3

## Usage
```
./scripts/json_dumper file.c | ./scripts/generator
```

## See also
   * [atd's documentation](http://atd.readthedocs.io/en/latest/)
   * [yojson's documentation](https://docs.mirage.io/yojson/Yojson/index.html)

## Contact
For more information send an e-mail to:

* Petr Peringer <peringer@fit.vutbr.cz> (corresponding author of JSON dumper)
* etc.
