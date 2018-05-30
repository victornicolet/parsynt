#include "stdio.h"

double _mps(double* a, int n) {
  double sum = 0.;
  double mps = 0.;
  long pos = 0;
  for(int i = 0; i < n; i++) {
    sum += a[i];
    mps = max(sum,mps);
    if(sum > mps){
        pos = i+1;
    }
  }
  return mps;
}

/* Join :
   sum = sum-l + sum-r
   mps = max(mps-l, mps-r + sum-l)
*/
