# Broom

Broom is a static analyzer for C written in OCaml.

## Building from sources

### List of dependencies
     - opam            >=  2.0.0
     - ocaml           >= 4.08.0
     - odoc
     - atdgen
     - core
     - cppo
     - dune
     - qtest
     - z3              >= 4.8.8-1

For JSON dumper see [code-listener/README](https://github.com/kdudka/predator/blob/master/README.md)

### Install dependencies

1. Install code-listener dependencies and opam:
  ```
  sudo apt install cmake gcc-10-multilib libboost-all-dev opam                              # for Ubuntu 20.04
  brew install cmake gcc@10 boost boost-build coreutils opam                                # for MacOS
  sudo dnf install opam cmake gmp-devel cmake boost-devel gcc-plugin-devel glibc-devel.i686 # for Fedora 33
  ```
2. Opam setup:
  ```
  $COMPILER="ocaml-variants.4.09.1+flambda"
  $SWITCH=$COMPILER
  
  opam init
  opam switch create $SWITCH $COMPILER
  eval `opam config env`
  opam update
  ```
3. Install dependencies by opam:
  ```
  cd broom
  opam install --deps-only broom .
  ```

### Build
```
cd broom             # continue in this directory
                     # for custom installation of gcc, set $GCC_HOST
./build.sh           # build code-listener dependency
make build           # build Broom tool
```

### Troubleshooting

* Empty the `code-listener` directory:
  ```
  git clone --recurse-submodules https://<URL>/broom.git
  ```
* `ld: warning: directory not found for option '-L/opt/local/lib'` appears
  during compilation on MacOS. The cause is `zarith` (dependence from Z3).
  To suppress the message, create the `/opt/local/lib` folder.

* Z3 Installation failed on MacOS with `clang: error: unsupported option '-fopenmp'`:
  Z3 <=4.8.1 requires a compiler with OpenMP support. The minimum required
  version of Z3 is 4.8.8-1.

To run the tests:
```
make check
```
## Usage
```
./scripts/broom [OPTs] file.c                             # main binary
./scripts/contract-generator file.c                       # print contracts
./scripts/call_graph file.c            # create DOTs (call graph, CFGs) from C
./scripts/json_dumper [-m32] file.c > file.json           # create JSON from C
./scripts/test
```

This will show you the available options of the Broom itself
(detailed description [here](options.md)):

```
./scripts/broom -h
```

## See also [for developers]
   * [atd's documentation](http://atd.readthedocs.io/en/latest/)
   * [yojson's documentation](https://docs.mirage.io/yojson/Yojson/index.html)

## Contact
For more information send an e-mail to:

* Anonymous author <anonymus@anonymus.org>
