/*
Reasoning for annotations:
- Slight variation in boundary checks or arithmetic.
- Function contract ensures bounds and correctness of return value.
- Loop annotations enforce safe access and correctness.
*/

/*@
 @ requires n > 0;
 @ requires \valid_read(arr + (0..n-1));
 @ requires \forall integer i; 0 <= i < n-1 ==> arr[i] <= arr[i+1];
 @ assigns \nothing;
 @ ensures \result == -1 || (0 <= \result < n && arr[\result] == key);
*/
int binarySearch(int arr[], int n, int key) {
  int start = 0, end = n - 1;
  /*@
    @ loop invariant 0 <= start && end < n && start <= end + 1;
    @ loop assigns start, end;
    @ loop variant end - start;
  */
  while (start <= end) {
    int mid = start + (end - start) / 2;
    if (arr[mid] == key)
      return mid;
    else if (arr[mid] < key)
      start = mid + 1;
    else
      end = mid - 1;
  }
  return -1;
}
