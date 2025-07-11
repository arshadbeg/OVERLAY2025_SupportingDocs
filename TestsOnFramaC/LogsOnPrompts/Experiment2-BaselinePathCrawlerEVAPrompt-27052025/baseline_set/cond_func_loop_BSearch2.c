/*
Reasoning for annotations:
- Another version of binary search, potentially with slight logic variation.
- Same loop contracts apply: we track index bounds and maintain a termination measure.
*/

/*@
 @ requires n > 0;
 @ requires \valid_read(arr + (0..n-1));
 @ requires \forall integer i; 0 <= i < n-1 ==> arr[i] <= arr[i+1];
 @ assigns \nothing;
 @ ensures \result == -1 || (0 <= \result < n && arr[\result] == key);
*/
int binarySearch(int arr[], int n, int key) {
  int left = 0, right = n - 1;
  /*@
    @ loop invariant 0 <= left && right < n && left <= right + 1;
    @ loop assigns left, right;
    @ loop variant right - left;
  */
  while (left <= right) {
    int mid = left + (right - left) / 2;
    if (arr[mid] == key)
      return mid;
    else if (arr[mid] < key)
      left = mid + 1;
    else
      right = mid - 1;
  }
  return -1;
}
