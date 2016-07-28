#include "stdio.h"

/* int sum_array(int* a, int n) { */
/*   int sum = 0; */
/*   for (int i = 0; i < n; i++) { */
/*     sum += a[i]; */
/*   } */
/*   return sum; */
/* } */

int mps_array(int* a, int n) {
  int sum = 0;
  int mps = 0;
  for(int i = 0; i < n; i++) {
    sum += a[i];
    mps = max (sum, mps);
  }
  return mps;
}
