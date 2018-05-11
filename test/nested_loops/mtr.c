#include "stdio.h"

int _mtlr(int** a, int* c, int n) {
  int* colmax;
  int r_mts = 0;
  int r_mss = 0;
  int mtr = 0;
  int sum;

  for (int i = 0; i < n; i++) {
	sum = 0;
	r_mts = 0;

    for(int j = 0; j < n; j++){
	  c[j] += a[i][j];
	  r_mts = max(c[j] + r_mts, 0);
	  r_mss = max(r_mts, r_mss);
    }
  }
  return mtr;
}
