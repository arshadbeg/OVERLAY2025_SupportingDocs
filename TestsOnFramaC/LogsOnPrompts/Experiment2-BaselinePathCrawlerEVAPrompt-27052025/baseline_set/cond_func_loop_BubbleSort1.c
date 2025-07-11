/*
Reasoning for annotations:
- Implements Bubble Sort: outer and inner loops compare and swap.
- Annotations ensure sorted output and track loop behavior with invariants and variants.
*/
/*@
  @ requires n > 0;
  @ requires \valid(arr + (0..n-1));
  @ assigns arr[0..n-1];
  @ ensures \forall integer i, j;
      0 <= i <= j < n ==> \at(arr[i], Post) <= \at(arr[j], Post);
*/
void bubbleSort(int arr[], int n) {
  /*@
    @ loop invariant 0 <= i <= n;
    @ loop assigns i, arr[0..n-1];
    @ loop variant n - i;
  */
  for (int i = 0; i < n - 1; i++) {
    /*@
      @ loop invariant 0 <= j < n - i;
      @ loop assigns j, arr[0..n-1];
      @ loop variant n - i - j;
    */
    for (int j = 0; j < n - i - 1; j++) {
      if (arr[j] > arr[j + 1]) {
        int temp = arr[j];
        arr[j] = arr[j + 1];
        arr[j + 1] = temp;
      }
    }
  }
}

