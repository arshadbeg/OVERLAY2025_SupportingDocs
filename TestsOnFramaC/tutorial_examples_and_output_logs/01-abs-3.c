// frama-c -wp -rte -wp-smoke-tests 01-abs-3.c
#include "limits.h"
/*@ requires x < INT_MIN;
    ensures (x >= 0 ==> \result == -x);
    ensures (x < 0 ==> \result == x);
    assigns \nothing;
*/
int abs ( int x ) {
  if ( x >=0 )
    return x ;
  return -x ;
}
