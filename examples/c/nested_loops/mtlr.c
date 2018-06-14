#include "stdio.h"

int _mtlr(int** a, int m, int n) {
  int *c;
  int mtr = 0;
  int mtrl = 0;
  int sum;

  for (int i = 0; i < n; i++) {
	sum = 0;
	mtr = 0;
    for(int j = 0; j < m; j++){
	  sum += a[i][j];
	  c[j] += sum;
	  mtr = max(c[j], mtr);
    }
	mtrl = max(mtr, mtrl);
  }
  return mtrl;
}
