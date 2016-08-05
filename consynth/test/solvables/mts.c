#include "stdio.h"


int mts(int* a, int n) {
  int sum = 0, mts = 0;

  for(int i = 0 ; i < n; i++) {
    sum += a[i];
    mts = max(0, mts + a[i]);
  }
  return mts + sum;
}

/*
  (define (__join__ $L $R)
  (let ...)
  ($ (+ sum-$R sum-$L) (max mts-$R (+ mts-$L sum-$R))))

  (define __$0__ ($ 0 0))
*/
