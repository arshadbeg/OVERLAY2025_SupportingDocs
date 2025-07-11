/*@
  @ requires \valid_read(a + (0..2));
  @ requires \valid_read(b + (0..2));
  @ assigns \nothing; // Conservative top-level view — inner loops modify k locally
  @ ensures \result == 0 || \result == 1;
*/
int uninit_var(int a[3], int b[3]) {
  int i, k;
  /*@
    @ loop invariant 0 <= i <= 2;
    @ loop assigns i, k;
    @ loop variant 2 - i;
  */
  for(i=0; i<2; i++) {     // line 3
      if(a[i] == 0)        // line 4
        return 0;
      if(a[i] != a[i+1])   // line 6
        k = 0;
      else
        /*@ 
          @ assert k == 0 || k == 1 || k == 2; // unsafe: k may be uninitialized
        */
        if(k == 2)         // line 9
          return 0;
      /*@
        @ loop assigns k;
        @ loop invariant 0 <= k <= 2;
        @ loop variant 2 - k;
      */
      while(b[k] != a[i])  // line 11
          if(k == 2)       // line 12
            return 0;
          else
            k++;
  }
  return 1;
}
