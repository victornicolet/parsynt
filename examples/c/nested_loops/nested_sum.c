#include "stdio.h"

int nsum(int** a, int n) {
  int sum = 0;
  int sumbis = 0;
  for (int i = 0; i < n; i++) {
	sum = 0;
    for(int j = 0; j < n; j++){
          sum += a[i][j];
    }
    sumbis += sum;
  }
  return sumbis;
}

/*
   Join found without auxiliary variable :

   sum = sum-l + sum-r

   in 1.692 s
*/
