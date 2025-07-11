/*
Reasoning for annotations:
- This file performs binary search using a loop.
- We annotate the loop with invariants, assigns clause, and a variant to ensure termination.
- The function is annotated with preconditions on array bounds and sorted order.
*/

/*@
 @ requires n > 0;
 @ requires \valid_read(arr + (0..n-1));
 @ requires \forall integer i; 0 <= i < n-1 ==> arr[i] <= arr[i+1];
 @ assigns \nothing;
 @ ensures \result == -1 || (0 <= \result < n && arr[\result] == key);
*/
int binarySearch(int arr[], int n, int key) {
  int low = 0, high = n - 1;
  /*@
    @ loop invariant 0 <= low && high < n && low <= high + 1;
    @ loop assigns low, high;
    @ loop variant high - low;
  */
  while (low <= high) {
    int mid = (low + high) / 2;
    if (arr[mid] == key)
      return mid;
    else if (arr[mid] < key)
      low = mid + 1;
    else
      high = mid - 1;
  }
  return -1;
}
