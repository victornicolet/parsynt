#include "stdio.h"

int _mps(int* a, int n) {
  int sum = 0;
  int mps = 0;
  for(int i = 0; i < n; i++) {
    sum += a[i];
    mps = max (sum, mps);
  }
  return mps;
}

/* Join :
   sum = sum-l + sum-r
   mps = max(mps-l, mps-r + sum-l)
*/
