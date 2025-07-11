/* ivette -wp -rte 05-abs-1.c */

#include<limits.h>

/*@ requires x > INT_MIN;

    assigns \nothing;

    behavior pos: 
      assumes x >= 0;
      ensures \result == x;

    behavior neg:
      assumes x < 0;
      ensures \result == -x;

    complete behaviors;
    disjoint behaviors;
*/
int abs ( int x ) {
  if ( x >=0 )
    return x ;
  return -x ;
}
