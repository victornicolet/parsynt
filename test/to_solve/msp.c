#include "stdio.h"

/*
   Maximum segment product:
   return the maximum of all products of the segments in the array.
 */
int example_msp(int* a, int n) {
  int msp = 1;
  int p1 = 1;
  int p2 = 1;

  for(int i = 0 ; i < n; i++) {
    if(a[i] > 0) {
      p1 = max(p1 * a[i], 1);
      p2 = min(p2 * a[i], 1);
    } else {
      tmp = p1;
      p1 = max(p2 * a[i], 1);
      p2 = min(p1 * a[i], 1);
    }
    msp = max(msp, p1);
  }
  return mtp;
}
