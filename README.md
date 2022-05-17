# Broom

Broom is a static analyzer for C written in OCaml. Broom primarily aims at programs that use low-level pointer manipulation to deal with various kinds of linked lists. It is based on separation logic and the principle of bi-abductive reasoning.

## Building from sources

### List of dependencies
     - opam            >=  2.0.0
     - ocaml           >= 4.08.0
     - odoc
     - atdgen
     - core
     - cppo
     - dune
     - z3              >= 4.8.8-1

For the JSON dumper see [code-listener/README](https://github.com/kdudka/predator/blob/master/README.md)

### Install dependencies

1. Install code-listener dependencies and opam:
  ```
  sudo apt install cmake g++-10-multilib gcc-10-plugin-dev libboost-all-dev opam libgmp-dev  # for Ubuntu 20.04
  brew install cmake gcc@10 boost boost-build coreutils opam                          # for MacOS
  sudo dnf install opam cmake gmp-devel boost-devel gcc-plugin-devel glibc-devel.i686 # for Fedora 33
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
  git clone --recurse-submodules https://pajda.fit.vutbr.cz/rogalew/broom.git
  ```
* `ld: warning: directory not found for option '-L/opt/local/lib'` appears
  during compilation on MacOS. The cause is `zarith` (dependence from Z3).
  To suppress the message, create the `/opt/local/lib` folder.

* Z3 Installation failed on MacOS with `clang: error: unsupported option '-fopenmp'`:
  Z3 <=4.8.1 requires a compiler with OpenMP support. The minimum required
  version of Z3 is 4.8.8-1.

## Usage
```
./scripts/broom [OPTs] -- file.c                          # main binary
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

* Adam Rogalewicz <rogalew@fit.vut.cz>
* Veronika Šoková <isokova@fit.vut.cz>
* Tomáš Vojnar
* Florian Zuleger
* Lukáš Holík
* Petr Peringer <peringer@fit.vut.cz> (corresponding author of JSON dumper)

Former Broom team members:

* Jens Pagel
