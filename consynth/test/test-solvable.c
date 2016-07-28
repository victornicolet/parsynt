#include "stdio.h"

/* int sum_array(int* a, int n) { */
/*   int sum = 0; */
/*   for (int i = 0; i < n; i++) { */
/*     sum += a[i]; */
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

int mts_array(int* a, int n) {
  int mts = 0;
  int sum = 0;
  for(int i = 0; i < n; i++) {
    sum = sum + a[i];
    mts = max (0, mts + a[i]);
  }
  return mts;
}

int mss_array(int* a, int n) {
  int mts = 0;
  int sum = 0;
  int mps = 0;
  int mss = 0;

  for(int i = 0; i < n; i++) {
    sum = sum + a[i];
    mts = max (0, mts + a[i]);
    mps = max (sum, mps);
    mss = max (mss, mts + a);
  }
  return mts;
}
