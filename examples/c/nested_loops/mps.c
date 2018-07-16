#include "stdio.h"

int _sum(int*** a, int m, int n, int o) {
  int mps = 0;
  int sum = 0;

  for (int i = 0; i < m; i++) {
    for(int j = 0; j < n; j++){
        for(int k = 0; k < o; k++){
          sum+= a[i][j][k];
        }
        mps = max(mps,sum);
    }
  }
  return sum;
}
