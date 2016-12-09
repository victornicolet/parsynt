#include "stdio.h"


int mts(int* a, int n) {
  int mts = 5;

  for(int i = 0 ; i < n; i++) {
    mts = max(5, mts + a[i]);
  }
  return mts;
}

/*
   Auxiliary variable found (sum):
   aux_1 = aux_1 + a[i]

   Join found with the auxiliary:
   aux_1 = aux_1-l + aux_1-r
   mts = max (mts-l + aux_1-r, mts-r)

   in 6.490 s
*/
