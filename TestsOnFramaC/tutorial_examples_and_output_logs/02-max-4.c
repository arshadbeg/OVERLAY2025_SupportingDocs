/* ivette -wp -rte 02-max-4.c */

/*@
  ensures \result >= a && \result >= b ;
  ensures \result == a || \result == b ;
  assigns \nothing;
*/
int max(int a, int b){
  return (a >= b) ? a : b ;
}
   
extern int x ;
   
int main(){
  x = 3;
  int r = max(4,2);
  //@ assert r == 4 ;
  //@ assert x == 3 ;
}
