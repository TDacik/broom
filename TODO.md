## TODO

- [x] calling functions with arguments;
  bug: [tomas-test-01.c](tests/tomas-test-01.c#L14)

- [x] global variables

- [ ] accessors
  - [x] reference
  - [x] dereference; bug: [easy-08-ok.c](tests/easy-08-ok.c#L13)
  - [ ] array dereference
  - [x] record accessor
  - [x] offset
  <br/>
- [ ] stack allocation and static storage in logic;
  instruction and functions: `clobber`, `__builtin_stack_restore`, `__builtin_stack_save`;
  bug: [easy-12-err.c](tests/easy-12-err.c#L9), [tomas-test-01.c](tests/tomas-test-01.c#L14)
    1. edit Formula/Z3, to accept `invalid(x)`, `stack(x,y)`, `static(x,y)`
    2. extend Z3 checks for `invalid` and `freed`
    3. edit contracts
    4. post-clobber - remove specific points-to on stack
    5. post-return/simplify remove all points-to on stack
    6. not allow stack/static in abstraction
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
  - [x] `free` - not implemented: value of pointer after free is not guaranteed (=undef) [tomas-test-02.c](tests/tomas-test-02.c)
  - [ ] `alloca` / `__builtin_alloca` / `__builtin_alloca_with_align`
  - [ ] `memchr`
  - [ ] `memcmp`
  - [ ] `memcpy`
  - [ ] `memmove`
  - [ ] `memset`
  - [x] `rand`
  - [x] `abort`
  - [ ] `assert` / `__assert_fail` / `__assert_rtn`
  - [x] `exit`
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
