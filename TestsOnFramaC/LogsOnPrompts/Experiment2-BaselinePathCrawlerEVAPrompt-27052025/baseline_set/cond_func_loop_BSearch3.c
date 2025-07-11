/*
Reasoning for annotations:
- Similar structure, but uses slightly different loop logic.
- Ensures correct array access, sortedness, and termination tracking.
*/

/*@
 @ requires n > 0;
 @ requires \valid_read(arr + (0..n-1));
 @ requires \forall integer i; 0 <= i < n-1 ==> arr[i] <= arr[i+1];
 @ assigns \nothing;
 @ ensures \result == -1 || (0 <= \result < n && arr[\result] == key);
*/
int binarySearch(int arr[], int n, int key) {
  int first = 0, last = n - 1;
  /*@
    @ loop invariant 0 <= first && last < n && first <= last + 1;
    @ loop assigns first, last;
    @ loop variant last - first;
  */
  while (first <= last) {
    int mid = first + (last - first) / 2;
    if (arr[mid] == key)
      return mid;
    else if (key > arr[mid])
      first = mid + 1;
    else
      last = mid - 1;
  }
  return -1;
}
