# Broom options

Default option in **bold**.

| Options                        | Description |
| ------------------------------ | --- |
| `-h,-help,--help`              | Help |
| `--version`                    | Show version number and exit ||
| `--compiler-options CFLAGS`    | C compiler options (e.g. --compiler-options "-m32 -g")|
| `--verbose <uint>`             | Turn on verbose mode (0-4)
| `--oom`                        | Simulate possible shortage of memory (heap allocation e.g. `malloc`, `calloc` can fail) |
| `--no-rerun`                   | Disable the second run|
| `--main <string>`              | Set name of entry function for initialization of global variables (<b>default is `main`</b>)|
| `--exit-leaks`                 | Report memory leaks of static variables at the end of program (while executing a no-return function or `main`)|
| `--no-exit-leaks`              | Not report memory leaks while executing a no-return function |
| `--memory_leaks_as_errors`     | Report memory leaks as errors otherwise warnings|
| `--abstraction-mode <uint>`    | Using of Slseg (Singly-linked List Segment) and Dlseg (Double-linked List Segment) abstraction: <ol><li value="0">disabled</li> <b><li>after entailment unsucceed</li></b> <li>before entailment</li></ol> |
| `--abstract-on-call`           | Additionally perform abstraction after each just completed call on caller's side|
| `--close-lambda`               | EXPERIMENTAL: proceed close lambdas within the abstraction|
| `--entailment-limit <uint>`    | Number of loop unfoldings used to stop the loop analysis when a fixpoint is not computed within a given number of loop iterations <ol><li value="0">unlimited</li> <b><li value="5">default</li></b> </ol> |
| `--abduction-strategy <uint>`  | Abduction strategy: <ol><b><li value="0"> standard strategy, for one result </b> <li>multiple strategies, more results </li></ol>|
| `--timeout <uint>`             | Set Z3 timeout for symbolic execution (in ms), <b>default is 2000ms</b>|
| `--timeout-simplify <uint>`    | Set Z3 timeout for formula simplification in states (in ms), <b>default is 100ms</b>|
| `--timeout-abstraction <uint>` | Set Z3 timeout for widening (in ms), <b>default is 200ms</b>|
| `--display-stats`              | Display statistics|
| `--dry-run`                    | Do not run the analysis|
| `--print-cl`                   | Dump linearized CL code on standard output|
| `--print-contracts`            | Dump linearized CL code with contracts on standard output |
