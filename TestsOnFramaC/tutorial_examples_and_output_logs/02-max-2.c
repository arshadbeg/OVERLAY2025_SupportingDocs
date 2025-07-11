/* ivette -wp -rte 02-max-2.c */

#include <limits.h>

/*@
  ensures \result >= a && \result >= b ;
*/
int max(int a, int b){
  return INT_MAX ;
} 
// wrong implementation
