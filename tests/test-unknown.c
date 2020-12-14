void f(void **p) {
   void * q;
   *p = q;
}  

int main() {
  void *x=0;
  void **xx = &x; 
  f(xx);
  return 0;
}
