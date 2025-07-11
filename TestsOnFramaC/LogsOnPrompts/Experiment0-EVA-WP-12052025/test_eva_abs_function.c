#include <stdio.h>

int abs_val(int x) {
  if (x < 0)
    return -x;
  else
    return x;
}

int main() {
  int a = -5;
  int b = abs_val(a);
  printf("Absolute value: %d\n", b);
  return 0;
}