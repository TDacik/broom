# Example

This section is true for Broom v0.0.1. Here is a simple [C program](tests/easy-01b-err.c) with an error to illustrate how Broom works.

```c
#include <stdlib.h>

/* error: dereference of NULL value */

int s(int *p) {
	int a;
	if (p == NULL)
		a = *p; // invalid deref if (p == NULL)
	else
		a = 0;
	return a;
}
```

Running `./scripts/broom -- tests/easy-01b-err.c` will produce this output. You can see reports during execution and final contracts for functions.

```
broom/code-listener/cl/cl_easy.cc:83: note: clEasyRun() took 0.000 s [internal location] [-fplugin=libjson.so]

>>> executing function s(%mF1:p):
tests/easy-01b-err.c:8:5:error: error from call of %mF3:a := *%mF1:p
===============================================
FUNCTIONS: 1
>>> spec of function s(%mF1:p):
Count of Contract EVARS: 3
LHS: (%mF1:p_anch=%c1) & (%c1!=NULL) & (%c2=(%c1=NULL)) & (%c2=false)
RHS: (%mF1:p_anch=%c1) & (%c2=(%c1=NULL)) & (%c1!=NULL) & (%c2=false) & (%ret=%c3) & (%c3=0)
Prog. VARS moves:
[error]Count of Contract EVARS: 1
LHS: (%mF1:p_anch=NULL) & (%c1=(%mF1:p_anch=NULL)) & (%c1=true)
RHS:
Prog. VARS moves:
===============================================
```

Running `./scripts/broom  --display-stats -- tests/easy-01b-err.c` will produce same output with statistics. Keep in mind that an error can be counted more than once if different paths lead to it.

```
Number of successful entailments: 0
Number of discard preconditions after rerun : 0
Number of internals: 0
Number of errors: 1
Number of warnings: 0
```

Running `./scripts/broom --print-cl --dry-run -- tests/easy-01b-err.c` will produce a C program in the Code Listener (CL) form to be analyzed by Broom.

```
broom/code-listener/cl/cl_easy.cc:83: note: clEasyRun() took 0.000 s [internal location] [-fplugin=libjson.so]
s(%mF1:p):
	L1:
		%rF2 := (%mF1:p == NULL)
		if (%rF2)
			goto L2
		else
			goto L3
	L2:
		%mF3:a := *%mF1:p
		goto L4
	L3:
		%mF3:a := 0
		goto L4
	L4:
		%rF4 := %mF3:a
		goto L5
	L5:
		return %rF4

```

Running `./scripts/broom --verbose=3 -- tests/easy-01b-err.c` will produce extended report of symbolic execution. The current state is printed for each CL instruction.

```
broom/code-listener/cl/cl_easy.cc:83: note: clEasyRun() took 0.000 s [internal location] [-fplugin=libjson.so]

>>> executing function s(%mF1:p):
>>> executing block L1:
		%rF2 := (%mF1:p == NULL)
EXISTS:
MISS: (%mF1:p_anch=%mF1:p) & (%mF1:p!=NULL)
CURR: (%mF1:p_anch=%mF1:p) & (%rF2=(%mF1:p=NULL)) & (%mF1:p!=NULL)
EXISTS:
MISS: (%mF1:p_anch=%mF1:p) & (%mF1:p=NULL)
CURR: (%mF1:p_anch=%mF1:p) & (%rF2=(%mF1:p=NULL)) & (%mF1:p=NULL)
		if (%rF2)
			goto L2
		else
			goto L3
EXISTS:
MISS: (%mF1:p_anch=%mF1:p) & (%mF1:p=NULL) & (%rF2=(%mF1:p=NULL)) & (%rF2=true)
CURR: (%mF1:p_anch=%mF1:p) & (%rF2=(%mF1:p=NULL)) & (%mF1:p=NULL) & (%rF2=true)
EXISTS:
MISS: (%mF1:p_anch=%mF1:p) & (%mF1:p!=NULL) & (%rF2=(%mF1:p=NULL)) & (%rF2=false)
CURR: (%mF1:p_anch=%mF1:p) & (%rF2=(%mF1:p=NULL)) & (%mF1:p!=NULL) & (%rF2=false)
>>> executing block L3:
		%mF3:a := 0
EXISTS:
MISS: (%mF1:p_anch=%mF1:p) & (%mF1:p!=NULL) & (%rF2=(%mF1:p=NULL)) & (%rF2=false)
CURR: (%mF1:p_anch=%mF1:p) & (%rF2=(%mF1:p=NULL)) & (%mF1:p!=NULL) & (%rF2=false) & (%mF3:a=0)
		goto L4
>>> executing block L4:
		%rF4 := %mF3:a
EXISTS:
MISS: (%mF1:p_anch=%mF1:p) & (%mF1:p!=NULL) & (%rF2=(%mF1:p=NULL)) & (%rF2=false) & (%mF3:a=0)
CURR: (%mF1:p_anch=%mF1:p) & (%rF2=(%mF1:p=NULL)) & (%mF1:p!=NULL) & (%rF2=false) & (%mF3:a=0) & (%rF4=%mF3:a)
		goto L5
>>> executing block L5:
		return %rF4
EXISTS:
MISS: (%mF1:p_anch=%mF1:p) & (%mF1:p!=NULL) & (%rF2=(%mF1:p=NULL)) & (%rF2=false) & (%mF3:a=0) & (%rF4=%mF3:a)
CURR: (%mF1:p_anch=%mF1:p) & (%rF2=(%mF1:p=NULL)) & (%mF1:p!=NULL) & (%rF2=false) & (%mF3:a=0) & (%rF4=%mF3:a) & (%ret=%rF4)
>>> final contract
Count of Contract EVARS: 3
LHS: (%mF1:p_anch=%c1) & (%c1!=NULL) & (%c2=(%c1=NULL)) & (%c2=false)
RHS: (%mF1:p_anch=%c1) & (%c2=(%c1=NULL)) & (%c1!=NULL) & (%c2=false) & (%ret=%c3) & (%c3=0)
Prog. VARS moves:
>>> executing block L2:
		%mF3:a := *%mF1:p
>>> final error contract
tests/easy-01b-err.c:8:5:error: error from call of %mF3:a := *%mF1:p
[error]Count of Contract EVARS: 1
LHS: (%mF1:p_anch=NULL) & (%c1=(%mF1:p_anch=NULL)) & (%c1=true)
RHS:
Prog. VARS moves:
===============================================
FUNCTIONS: 1
>>> spec of function s(%mF1:p):
Count of Contract EVARS: 3
LHS: (%mF1:p_anch=%c1) & (%c1!=NULL) & (%c2=(%c1=NULL)) & (%c2=false)
RHS: (%mF1:p_anch=%c1) & (%c2=(%c1=NULL)) & (%c1!=NULL) & (%c2=false) & (%ret=%c3) & (%c3=0)
Prog. VARS moves:
[error]Count of Contract EVARS: 1
LHS: (%mF1:p_anch=NULL) & (%c1=(%mF1:p_anch=NULL)) & (%c1=true)
RHS:
Prog. VARS moves:
===============================================
```

## Differences between the generated output and the description in the paper

Program variables (_PVars_):
 * `%mS<uid>:<name>` global scope variables in static storage
 * `%mF<uid>:<name>` function scope variables
 * `%rF<uid>` unnamed function scope variables (register given by compiler)

Logical variables (_LVars_):
 * `%l<uid>` logical/existential variables
 * `%mF<uid>:<name>_anch` anchor for arguments of function
 * `%ret`
 * `%c<uid>` contract variables (unique existential variables in contract)

Compared to the separation logic described in Section 5, Broom uses a slightly different notation:

*  _base(x) ≡ b(x)_
*  _len(x) ≡ e(x) - x_
*  _x-(c)->y_ stands for _x |-> y_ and we have _c = size(y)_; we write _c_ in the points-to arrow of the tool output in order to make it easier for the reader to track the size of y
*  _x-(size)->T_ stands for _x -> T[size]_ where 'size' is some expression
*  _x-(size)->0_ stands for _x -> 0[size]_ where 'size' is some expression

The axioms of page 9 from the paper then become

  _∀ l. len(l) ≥ 0 ∧ l ≥ base(l) ∧ len(base(l)) - l = len(l) ∧ base(l)=0 <-> len(l) = 0_

  _∀ l,l'. (0 < base(l) < l' <= base(l) + len(base(l)) ∨ 0 < base(l') < l <= base(l') + len(base(l'))) -> base(l) = base(l')_

Note that we can always recover _e(x)_ from this presentation by setting _b(x) = base(x)_ and _e(x) = base(x) + len(base(x))_.

For the current state formula denoted as _Q_ in the paper (and printed as _Curr_ by Broom), all variables that do not also appear in the pre-condition denoted as _P_ in the paper (and printed as _Miss_ by Broom) are assumed to be existentially quantified; however, we do not print the quantifiers in order not to clutter the presentation. For example, for _P: x = X ∧ X |-> Y_ and _Q:  x = X ∧ X |-> u_, the formula _Q_ has to be understood as _∃ u. x = X ∧ X |-> u_ because _u_ does not appear in the pre-condition _P_.
