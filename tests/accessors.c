#include <stdlib.h>

struct z {
	int item4;
};

struct y {
	struct z item3;
};

struct x {
	struct y item2;
};

struct s {
	struct x item1;
} s;


struct p {
	struct p * item1;
};

struct t {
	int arr[1][1];
};

struct u {
	struct t item2;
};

struct v {
	struct u *item1;
};

struct w {
	struct t item1;
	int item2;
	int arr[2];
} w;

int m[5][5][5];

extern struct w g(int arg1[1][1], struct t *arg2, int arg3[2]);

extern struct w f(struct w (*arg1)[5], int *arg2, struct t *arg3, int arg4[2]);

int main() {
	struct p ***ppp;

// 1. dereferences *p, **p, ***p

	struct p **pp = *ppp;
	/* pp := *ppp */
	struct p *p = **ppp;
	/* %reg1 := *ppp
	   p := *%reg1
	*/
	struct p sp = ***ppp;
	/* %reg2 := *ppp
	   %reg3 := *%reg2
	   sp := *%reg3
	*/

// 2. record accessors s.item1, s.item1.item2

	struct x x = s.item1;
	/* x := s.item1 */
	struct y y = s.item1.item2;
	/* y := s.item1.item2 */
	struct z z = s.item1.item2.item3;
	/* z := s.item1.item2.item3 */

// 3. (*p).item1, (*((*p).item1)).item2, ..., same as p->item1, p->item1->item2, ...

	p = p->item1;
	/* p := *p.item1 */
	p = p->item1->item1;
	/* %reg4 := *p.item1
	   p := *%reg4.item1
	*/
	p = p->item1->item1->item1;
	/* %reg5 := *p.item1
	   %reg6 := *%reg5.item1
	   p := *%reg6.item1
	*/

// 4. reference of dereference &(*p), &(**p), &(***p)

	p = &(*p);
	/* p := p */
	p = &(**pp);
	/* p := *pp */
	p = &(***ppp);
	/* %reg7 := *ppp
	   p := *%reg7
	*/
	p = &(*(&(**pp)));
	/* p := *pp */
	
	int *j = &(*((int*)p));
	/* j := p          j has different target type */

// 5. dereference of reference

	s = *(&s);
	/* s := s */
	short si = *((short *)&s);
	/* %reg8 := &s
	   si := *%reg8     *reg8 has different target type
	*/

// 5. &(s.item1), &(s.item1.item2)

	struct x *xx = &(s.item1);
	/* xx := &s.item1 */
	struct y *yy = &(s.item1.item2);
	/* yy := &s.item1.item2 */
	struct z *zz = &(s.item1.item2.item3);
	/* zz := &s.item1.item2.item3 */

// 6. &((*p).item1), &((*((*p).item1)).item2), ..., same as &(p->item1), &(p->item1->item2), ...

	pp = &(p->item1);
	/* pp := &*p.item1 */
	pp = &(p->item1->item1);
	/* %reg9 := *p.item1
	   pp := &*%reg9.item1
	*/
	pp = &(p->item1->item1->item1);
	/* %reg10 := *%p.item1
	   %reg11 := *%reg10.item1
	   %pp := &*%reg11.item1
	*/

	p->item1->item1->item1 = NULL;
	/* %reg12 := *p.item1
	   %reg13 := *%reg12.item1
	   *%reg13.item1 := NULL */

// 7. array dereference a[n] and offset a.<+n>
	
	int i = *(m[1][1] + 1);
	/* i := m[1][1][1] */
	i = *(*(m[1] + 1) + 1);
	/* %reg14 := (&m[1] [ptr]+ 24)
	   i := *%reg14
	*/
	i = *(*(*(m + 1) + 1) + 1);                              //BUG!!!!!
	/* i := m.<+124> */

	int (*b)[5] = *(m + 1); // 2D array[25]
	/* b := (&m [ptr]+ 100) */
	i = *(b[1] + 1);
	/* %r15 := (b [ptr]+ 20)
	   i := *%reg15.<+4>
	*/
	i = *(*(b + 1) + 1);
	/* %reg16 := (b [ptr]+ 20)
	   i := *%reg16.<+4>
	*/

	int *a = *(b + 1); // 1D array[5]
	/* a := (b [ptr]+ 20) */
	i = *(a + 1);
	/* i := *a.<+4> */

	a = &m[0][0][0]; // 1D array[125]
	/* a := &m[0][0][0] */

// 8. negative offset and record acc, array dereference

	int *shift_a = a + 2;

	i = *(shift_a - 1);
	/* i := *shift_a.<-4> */
	i = w.arr[-1];
	/* i := w.arr[(-1)] */

// 9. the longest combination

	struct v *v;

	a = &(w.item1.arr[0][0]);
	/* a := &w.item1.arr[0][0] */
	a = &(v->item1->item2.arr[0][0]);
	/* %reg17 := *v.item1
	   a := &*%reg17.item2.arr[0][0]
	*/
	
	struct v (*arr_v)[5]; // pointer to array of 5 structures

	v = (*arr_v)+ 1;
	a = &((*(v - 1)).item1->item2.arr[0][0]);
	/* %reg18 := (v [ptr]+ (-8))
	   %reg19 := *%reg18.item1
	   a := &*%reg19.item2.arr[0][0]
	*/


	struct w *ar_w[5];
	struct w *pw = *(ar_w + 1);

	a = &( ( *( (struct w *)*(ar_w + 1) ) ).item1.arr[0][0] );
	/* %reg20 := ar_w[1]
	   a := &*%reg20.item1.arr[0][0]
	*/

// 10. more operands

	sp.item1 = &sp;                                          //BUG!!!!!
	/* sp.item1 := &sp */

	ar_w[1] = (struct w *) &ar_w;                            //BUG!!!!!
	/* ar_w[1] := &ar_w */

	*(a + 1) = (int) &a;
	/* %reg21 := &a
	   %reg_a := a
	   %reg22 := (%reg_a [ptr]+ 4U)
	   %reg23 := %reg21
	   *%reg22 := %reg23
	*/
	
	*pp = (struct p *) &pp;
	/* %reg_pp := pp
	   *%reg_pp := &pp */
	
	w = g(w.item1.arr, &(w.item1), w.arr);
	/* w := g(&w.item1.arr, &w.item1, &w.arr) */
	
	struct w arr_w[5];
	
	arr_w[1] = f(&arr_w, &(arr_w[1].item1.arr[0][0]), &(arr_w[1].item1), arr_w[1].arr);
	/* arr_w[1] := f(&arr_w, &arr_w[1].item1.arr[0][0], &arr_w[1].item1, &arr_w[1].arr) */

	return 0;
}
