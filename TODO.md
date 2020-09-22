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
- [ ] stack allocation and static storage in logic
    ```
    int glob_var;
    &glob_var;   // c1 -(4)-> glob_var handled as heap allocation
  
    int local_var;
    &local_var;  // c1 -(4)-> local_var handled as heap allocation
  
    struct node {
      int i;
      int j;
    } a;         // c1 -(8)-> a & (base(c1)=c1)
    a.i=3;       // c1 -(4)-> c2 & (c2=3) & (base(c1)=c1)
                 // c3 -(4)-> Undef & (c3=c1+4) & (base(c3)=base(c1))
    ```
   instruction and fnctions: `clobber`, `__builtin_stack_restore`, `__builtin_stack_save` 

   bug: [easy-12-err.c](tests/easy-12-err.c#L9), [tomas-test-01.c](tests/tomas-test-01.c#L14)

- [x] sls abstraction

- [ ] dls abstraction in logic

- [x] entailment; bug: [sll2.c](tests/sll2.c), [unreach.c](tests/unreach.c)

- [ ] better error detection

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
  - [ ] `abort`
  - [ ] `exit`
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
