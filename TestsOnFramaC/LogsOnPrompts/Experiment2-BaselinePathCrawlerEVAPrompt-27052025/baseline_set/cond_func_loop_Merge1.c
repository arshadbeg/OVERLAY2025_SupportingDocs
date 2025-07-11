/*
Reasoning for annotations:
- Merge routine combines two sorted subarrays into one.
- Preconditions ensure valid memory and sorted subarrays.
- Postconditions can assert merged ordering.
*/

/*@
 @ requires left >= 0 && mid >= left && right > mid;
 @ requires \valid(a + (left..right));
 @ requires \forall integer i; left <= i < mid ==> a[i] <= a[i + 1];
 @ requires \forall integer i; mid < i < right ==> a[i] <= a[i + 1];
 @ assigns a[left..right];
 @ ensures \forall integer i; left <= i < right ==> a[i] <= a[i + 1];
*/
void merge(int a[], int left, int mid, int right) {
  int i = left, j = mid + 1, k = 0;
  int temp[right - left + 1];

  /*@
    @ loop invariant left <= i <= mid + 1 && mid + 1 <= j <= right + 1;
    @ loop assigns i, j, k, temp[0..right-left];
    @ loop variant (mid - i) + (right - j);
  */
  while (i <= mid && j <= right) {
    if (a[i] <= a[j])
      temp[k++] = a[i++];
    else
      temp[k++] = a[j++];
  }

  /*@ loop invariant i <= mid + 1;
      loop assigns i, k, temp[0..right-left];
      loop variant mid - i;
  */
  while (i <= mid)
    temp[k++] = a[i++];

  /*@ loop invariant j <= right + 1;
      loop assigns j, k, temp[0..right-left];
      loop variant right - j;
  */
  while (j <= right)
    temp[k++] = a[j++];

  /*@ loop invariant 0 <= m <= right-left;
      loop assigns a[left..right];
      loop variant right - left - m;
  */
  for (int m = 0; m < k; m++)
    a[left + m] = temp[m];
}
