#include "stdio.h"

/* int sum_array(int* a, int n) { */
/*   int sum = 0; */
/*   for (int i = 0; i < n; i++) { */
/*     sum += a[i]; */
/*   } */
/*   return sum; */
/* } */

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

/* int mps_array(int* a, int n) { */
/*   int sum = 0; */
/*   int mps = 0; */
/*   for(int i = 0; i < n; i++) { */
/*     sum += a[i]; */
/*     mps = max (sum, mps); */
/*   } */
/*   return mps; */
/* } */

int mss_array(int* a, int n) {
  int mts = 0;
  int sum = 0;
  int mps = 0;
  int mss = 0;

  for(int i = 0; i < n; i++) {
    sum = sum + a[i];
    mps = max (sum, mps);
    mss = max (mss, mts + a[i]);
    mts = max (0, mts + a[i]);
  }
  return mts;
}
