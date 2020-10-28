## TODO

- [x] calling functions with arguments; bug: argument with accessors [tomas-test-01.c](tests/tomas-test-01.c#L14)

- [x] global variables

- [ ] accessors
  - [x] reference
  - [x] dereference; bug: [easy-08-ok.c](tests/easy-08-ok.c#L13)
  - [ ] array dereference
  - [x] record accessor
  - [x] offset
  <br/>
- [ ] stack allocation and static storage in logic;
  bug: [alias-10.c](tests/alias-10.c#L15)
    - [ ] introduce `invalid(x)`, `stack(x,y)`, and `static(x,y)` predicates
        1. edit abduction, to correctly resolve `static(x,y)`
        2. not allow stack/static in abstraction
    - [x] `clobber`
    - [x] `alloca` / `__builtin_alloca`
    - [ ] `__builtin_alloca_with_align`
    - [ ] `__builtin_stack_restore`, `__builtin_stack_save`
  <br/>
- [x] sls abstraction

- [ ] dls abstraction in logic

- [x] entailment; bug: [sll2.c](tests/sll2.c), [unreach.c](tests/unreach.c)

- [ ] better error detection

- [ ] calling extern functions; `dst = fnc(&a)` means `dst=undef & a=undef`

- [ ] contracts for standard library functions (related to memory)
  - [x] `malloc`
  - [ ] `calloc`
  - [ ] `realloc`
  - [ ] `aligned_alloc` (since C11)
  - [x] `free` - not implemented: value of pointer after free is not guaranteed (=undef) [tomas-test-02.c](tests/tomas-test-02.c)
  - [ ] `memchr`
  - [ ] `memcmp`
  - [ ] `memcpy`
  - [ ] `memmove`
  - [ ] `memset`
  - [x] `rand`
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
- [ ] integer abstraction

- [ ] union type

- [ ] recursion

- [ ] functions with variable number of arguments

- [ ] float type
