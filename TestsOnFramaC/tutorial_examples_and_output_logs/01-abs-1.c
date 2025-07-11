/* 1. ivette -wp      01-abs-1.c */
/* 2. ivette -wp -rte 01-abs-1.c */

/*@ ensures (x >= 0 ==> \result == x) && 
      (x < 0 ==> \result == -x);
*/
int abs ( int x ) {
  if ( x >=0 )
    return x ;
  return -x ;
}
