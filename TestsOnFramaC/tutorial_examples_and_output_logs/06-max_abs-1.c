/* ivette -wp -rte 06-max_abs-1.c */

#include<limits.h>

/*@ 
  requires x > INT_MIN;
  ensures (x >= 0 ==> \result == x) && (x < 0 ==> \result == -x);
  assigns \nothing; 
*/
int abs ( int x );

/*@ 
  ensures \result >= x && \result >= y;
  ensures \result == x || \result == y;
  assigns \nothing; 
*/
int max ( int x, int y );

/*@ 
  ensures \result >= x && \result >= -x && \result >= y && \result >= -y;
  ensures \result == x || \result == -x || \result == y || \result == -y;
  assigns \nothing; 
*/
int max_abs( int x, int y ) {
  x=abs(x); 
  y=abs(y);
  return max(x,y);
}
