#include "stdio.h"

int _mtrr(int** a, int* c, int n) {
  int mtr = 0;
  int mtrr = 0;
  int sum = 0;

  for (int i = 0; i < n; i++) {
	sum = 0;
	mtr = 0;
    for(int j = 0; j < n; j++){
	  c[j] += a[i][j];
	  mtr = max(mtr + c[j], 0);
    }
	mtrr = max(mtr, mtrr);
  }
  return mtrr;
}
