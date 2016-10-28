#include "stdio.h"

int sum_array(int* a, int n) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    sum += a[i];
  }
  return sum;
}

/* (define (__join__ $L $R)
   (let ((sum-$L ($-sum $L)) (sum-$R ($-sum $R)))
   ($ (+ (add1 sum-$L) (sub1 sum-$R)))))
   (define __$0__ ($ 0)) */
