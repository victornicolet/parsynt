#include "stdio.h"

int mps_array(int* a, int n) {
  int sum = 0;
  int mps = 0;
  for(int i = 0; i < n; i++) {
    sum += a[i];
    mps = max (sum, mps);
  }
  return mps;
}

/* (define (__join__ $L $R)
   (let ((sum-$L ($-sum $L))
   (mps-$L ($-mps $L))
   (sum-$R ($-sum $R))
   (mps-$R ($-mps $R)))
   ($ (+ (add1 sum-$L) (sub1 sum-$R)) (max (max -4 mps-$L) (+ mps-$R sum-$L)))))
   (define __$0__ ($ 0 0)) */
