/* ivette -wp -rte 07-reset_array-1.c */

/*@
  requires 0 <= len;
  requires \valid(a + (0 .. len-1));
  assigns a[0 .. len-1];
  ensures \forall integer i ; 0 <= i < len ==> a[i] == 0;
*/
void reset_array(int* a, int len){
  /*@
    loop invariant 0 <= i <= len ;
    loop invariant 
      \forall integer j; 0 <= j < i ==> a[j] == 0 ;
    loop assigns i, a[0 .. len-1];
    loop variant len - i ;
  */
  for(int i = 0 ; i < len ; ++i){
    a[i] = 0 ;
  }
}
