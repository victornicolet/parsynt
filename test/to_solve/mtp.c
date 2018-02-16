#include "stdio.h"

/*
   Maximal terminal product:
   returns the product of a suffix of the array, such that this product is maximal.
*/

int example_mtp(int* a, int n) {
  int p1 = 1;
  int p2 = 1;
  int tmp = 1;

  for(int i = 0 ; i < n; i++) {
    if(a[i] > 0) {
      p1 = max(p1 * a[i], 1);
      p2 = min(p2 * a[i], 1);
    } else {
      tmp = p1;
      p1 = max(p2 * a[i], 1);
      p2 = min(p1 * a[i], 1);
    }
  }
  return max(p1,p2);
}
