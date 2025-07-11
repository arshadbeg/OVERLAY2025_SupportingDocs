/* ivette -wp -rte 02-max-1.c */

/*@
  ensures \result >= a && \result >= b ;
*/
int max(int a, int b){
  return (a >= b) ? a : b ;
}

extern int x ;

int main(){
  x = 3;
  int r = max(4, 2);
  //@ assert r == 4 ;
  //@ assert x == 3 ;
}
