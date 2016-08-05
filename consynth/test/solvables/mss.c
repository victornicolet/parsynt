#include "stdio.h"


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
  return mss;
}
/*
  (define (__join__ $L $R)
  (let ... )
  ($
  (max (max mts-$R 0) (+ mts-$L sum-$R)) ; mts
  (+ (min sum-$R sum-$L) (max sum-$L sum-$R)) ; sum
  (max mps-$L (+ sum-$L mps-$R)) ; mps
  (max (max mss-$R mss-$L) (+ mps-$R mts-$L))))) ; mss

  (define __$0__ ($ 0 0 0 0))
*/
