#include "stdio.h"

int example_nested_sum(int** a, int* c, int** K, int n) {
  int sum = 0;
  int sumbis = 0;
  for (int i = 0; i < n; i++) {
    for(int j = 0; j < n; j++){
          sum += a[i][j];
	  K[i][j] = sum;
    }
    sumbis += sum;
    c[i] = sum;
    sum = 0;
  }
  return sumbis;
}
