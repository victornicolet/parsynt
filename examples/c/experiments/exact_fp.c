#include "stdio.h"

int _mps(int* a, int n) {
  int sum = 0;
  int mps = 0;
  int pos = 0;
  for(int i = 0; i < n; i++) {
    sum += a[i];
    if(sum > mps){
        mps = sum;
        pos = i;
    }
  }
  return mps;
}

/* Join :
   sum = sum-l + sum-r
   mps = max(mps-l, mps-r + sum-l)
*/
