#include "stdio.h"

int _sum(int* a, int n) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    sum += a[i];
  }
  return sum;
}

/*
   Join found without auxiliary variable :

   sum = sum-l + sum-r

   in 1.692 s
*/
