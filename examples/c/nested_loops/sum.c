#include "stdio.h"

int _sum(int*** a, int m, int n, int o) {
  int sum = 0;
  int sumbis = 0;
  int sumter = 0;

  for (int i = 0; i < m; i++) {
    sumbis = 0;
    for(int j = 0; j < n; j++){
        sumter = 0;
        for(int k = 0; k < o; k++){
          sumter += a[i][j][k];
        }
        sumbis += sumter;
    }
    sum += sumbis;
  }
  return mps;
}
