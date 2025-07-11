/* ivette -wp -rte 03-max_ptr-3.c */

/*@ requires \valid(p) && \valid(q);
    ensures \result >= *p && \result >= *q;
    ensures \result == *p || \result == *q;
*/
int max_ptr ( int *p, int *q ) {
  *p = 0; 
  *q = 0;
  return 0 ;
}
