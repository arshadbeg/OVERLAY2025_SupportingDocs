/*@ ensures \forall integer k; 0 <= k < \old(n) ==> *(\old(a)+k) == 0; */
void job(int n, int *a)
{
   int i;
   i = 0;
   /*@ loop invariant 0 <= i <= n+1;
       loop invariant
          (\forall integer k; 0 <= k <= i ==> *(a+k) == 0) ||
          (\forall integer k; 0 <= k < n ==> *(a+k) == 1);
       loop assigns i, *(a+(0 .. n-1));
   */
   while (i < n) {
      *(a + i) = 0;
      i ++;
   }
   return;
}