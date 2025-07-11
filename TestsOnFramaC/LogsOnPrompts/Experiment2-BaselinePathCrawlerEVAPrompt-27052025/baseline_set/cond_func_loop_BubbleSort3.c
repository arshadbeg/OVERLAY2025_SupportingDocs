/*
Reasoning for annotations:
- This version starts inner loop from the end toward the start.
- Loop variant counts down instead of up.
*/

/*@
 @ requires n > 0;
 @ requires \valid(arr + (0..n-1));
 @ assigns arr[0..n-1];
 @ ensures \forall integer i, j; 0 <= i <= j < n ==> arr[i] <= arr[j];
*/
void bubbleSort(int arr[], int n) {
  /*@
    @ loop invariant 0 <= i <= n;
    @ loop assigns i, j, arr[0..n-1];
    @ loop variant n - i;
  */
  for (int i = 0; i < n; i++) {
    /*@
      @ loop invariant i < j <= n;
      @ loop assigns j, arr[0..n-1];
      @ loop variant j - i;
    */
    for (int j = n - 1; j > i; j--) {
      if (arr[j - 1] > arr[j]) {
        int temp = arr[j];
        arr[j] = arr[j - 1];
        arr[j - 1] = temp;
      }
    }
  }
}
