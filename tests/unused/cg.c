void g0_rec() {
	g0_rec();
}

void h0() {}

void e1() {
	g0_rec();
	h0();
}

void d1();

void f0_ind_rec() {
	d1();
}

void d1() {
	f0_ind_rec();
}

void a2() {
	d1();
	e1();
}

void c1() {}

void b2() {
	c1();
}
