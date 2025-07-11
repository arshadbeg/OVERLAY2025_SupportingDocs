#include <limits.h>

/*@
  requires INT_MIN <= *a + *b <= INT_MAX ;
  requires \valid(a) && \valid(b);
  requires \separated(a, b);
  assigns  *a;
  ensures  *a == \old(*a)+ *b;
*/
void incr_a_by_b(int* a, int* b){
  *a += *b;
}
