# Broom options

The default options are in **bold**.

| Options                        | Description |
| ------------------------------ | --- |
| `-h,-help,--help`              | Help |
| `--version`                    | Show the version number and exit ||
| `--compiler-options CFLAGS`    | C compiler options (e.g. --compiler-options "-m32 -g")|
| `--verbose <uint>`             | Turn on a verbose mode (0-4)
| `--oom`                        | Simulate possible shortage of memory (i.e., allow heap allocation, e.g., `malloc`, `calloc`, to fail) |
| `--no-rerun`                   | Disable the second phase of the analysis (checking soundness of candidate contracts) |
| `--main <string>`              | Set the name of the entry function for initialization of global variables (<b>default is `main`</b>)|
| `--exit-leaks`                 | Report memory leaks of static variables at the end of the program (while executing a no-return function or `main`)|
| `--no-exit-leaks`              | Do not report memory leaks while executing a no-return function |
| `--memory_leaks_as_errors`     | Report memory leaks as errors otherwise warnings|
| `--abstraction-mode <uint>`    | Usage of the Slseg (Singly-linked List Segment) and Dlseg (Double-linked List Segment) abstraction: <ol><li value="0">disabled</li> <b><li>after entailment fails</li></b> <li>before entailment</li></ol> |
| `--abstract-on-call`           | Additionally perform abstraction after each just completed call on the caller's side|
| `--close-lambda`               | EXPERIMENTAL: close lambdas within the abstraction|
| `--entailment-limit <uint>`    | Number of loop unfoldings used to stop loop analysis when a fixpoint is not computed within a given number of loop iterations <ol><li value="0">unlimited</li> <b><li value="5">default</li></b> </ol> |
| `--abduction-strategy <uint>`  | Abduction strategy: <ol><b><li value="0"> standard strategy (one result) </b> <li>multiple strategies (more results) </li></ol>|
| `--timeout <uint>`             | Set a Z3 timeout for the symbolic execution (in ms), <b>default is 2000ms</b>|
| `--timeout-simplify <uint>`    | Set a Z3 timeout for formula simplification (in ms), <b>default is 100ms</b>|
| `--timeout-abstraction <uint>` | Set a Z3 timeout for widening (in ms), <b>default is 200ms</b>|
| `--display-stats`              | Display statistics|
| `--dry-run`                    | Do not run the analysis|
| `--print-cl`                   | Dump linearized CL code on the standard output|
| `--print-contracts`            | Dump linearized CL code with contracts on the standard output |
