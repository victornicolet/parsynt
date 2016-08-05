#include "stdio.h"

/* int sum_2 (int* a, int* b, int n) { */
/*   int sum = 0; */
/*   for (int i = 0; i < n; i++) { */
/*     sum += a [i]; */
/*     for(int j = 0; j < n; j ++) { */
/*       sum += b [i]; */
/*     } */
/*   } */
/*   return sum; */
/* } */

int mps(int* a, int n) {
  int sum = 0, mts = 0;

  for(int i = 0 ; i < n; i++) {
    sum += a[i];
    mts = max(0, mts + a[i]);
  }
  return mts + sum;
}
