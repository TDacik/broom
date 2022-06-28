## TODO

- [x] basic instructions; bug: subptr no memory leak [easy-15c-err.c](easy-15c-err.c); bug: no warning: [test-different-block-pointer-comparison.c](test-different-block-pointer-comparison.c)

- [x] calling functions with arguments; not implemented: argumnets overlap: [args_overlap-err.c](args_overlap-err.c) argument with accessors ?

- [x] global variables

- [ ] control flow graph

- [x] accessors; bug: abduction rules for variable offset [alias-10.c](alias-10.c#L16)
  - [x] reference
  - [x] dereference
  - [x] array dereference
  - [x] record accessor
  - [x] offset
  <br/>
- [ ] stack allocation and static storage in logic; not implemented: [call-01-ok.c](call-01-ok.c), [easy-12-ok.c](easy-12-ok.c), [easy-12b-err.c](easy-12b-err.c), [easy-12c-err.c](easy-12c-err.c), [easy-15b-ok.c](easy-15b-ok.c), [easy-16-err.c](easy-16-err.c), [easy-16b-err.c](easy-16b-err.c), [easy-17-ok.c](easy-17-ok.c), [easy-18-err.c](easy-18-err.c), [easy-18b-err.c](easy-18b-err.c), [easy-20-ok.c](easy-20-ok.c); bug: uninitialized value [easy-19-err.c](easy-19-err.c)
    - [x] introduce `invalid(x)`, `stack(x,y)`, and `static(x,y)` predicates
        1. not allow stack/static in abstraction
    - [x] `clobber`
    - [x] `alloca` / `__builtin_alloca`
    - [ ] `__builtin_alloca_with_align`
    - [ ] `__builtin_stack_restore`, `__builtin_stack_save`
  <br/>
- [x] sls abstraction
    - [ ] shared nested subheap
  <br/>
- [x] dls abstraction in logic
    - [ ] shared nested subheap
  <br/>
- [x] entailment; bug: [unreach.c](unreach.c)

- [ ] better error detection - not implemented: no applicable contract: [abort.c](abort.c), [easy-03-err.c](easy-03-err.c), [easy-14-err.c](easy-14-err.c), [global-mem-leaks.c](global-mem-leaks.c), [global-err.c](global-err.c), [stack-err.c](stack-err.c); not implemented: mergin preconditions: [nondet-err.c](nondet-err.c), [nondet2-err.c](nondet2-err.c), [nondet3-err.c](nondet3-err.c)

- [ ] calling extern functions; `dst = fnc(&a)` means `dst=undef & a=undef`

- [ ] contracts for standard library functions (related to memory)
  - [x] `malloc`; big: oom [malloc-oom.c](malloc-oom.c)
  - [ ] `calloc`
  - [ ] `realloc`
  - [ ] `aligned_alloc` (since C11)
  - [x] `free` - not implemented: value of pointer after free is not guaranteed (=undef) [tomas-test-02.c](tomas-test-02.c)
  - [ ] `memchr`
  - [ ] `memcmp`
  - [x] `memcpy`
  - [ ] `memmove`
  - [x] `memset`
  - [x] `rand`; bug: [unsigned.c](unsigned.c)
  - [x] `abort`
  - [ ] `assert` / `__assert_fail` / `__assert_rtn`
  - [x] `exit` - not implemented: calling `atexit` registred functions
  - [x] `_Exit`
  - [ ] `atexit`
  <br/>
- [ ] string type

- [ ] contracts for standard library functions with strings
  - [ ] `strchr`
  - [ ] `strcmp`
  - [ ] `strncmp`
  - [ ] `strcpy` (warning)
  - [ ] `strncpy`
  - [ ] `strlen`
  - [ ] `printf`
  - [ ] `puts`
  <br/>
- [ ] integer abstraction; [arithmetic.c](arithmetic.c)

- [ ] union type

- [ ] recursion; [cg.c](cg.c)

- [ ] function pointers (callbacks)

- [ ] functions with variable number of arguments

- [ ] float type
