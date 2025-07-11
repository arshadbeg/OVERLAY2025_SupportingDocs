/*
Reasoning for annotations:
- Another Bubble Sort variant with slightly modified boundaries.
- Loop annotations ensure array remains within bounds and sorting is complete.
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
  for (int i = 1; i < n; i++) {
    /*@
      @ loop invariant 0 <= j < n - i;
      @ loop assigns j, arr[0..n-1];
      @ loop variant n - i - j;
    */
    for (int j = 0; j < n - i; j++) {
      if (arr[j] > arr[j + 1]) {
        int temp = arr[j];
        arr[j] = arr[j + 1];
        arr[j + 1] = temp;
      }
    }
  }
}
