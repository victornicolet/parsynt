#include "stdio.h"

int example_mtlr(int** a, int* c, int n) {
  int* colmax;
  int mtr = 0;
  int mtrl = 0;
  int sum;

  colmax = malloc(sizeof(int) * n);

  for (int i = 0; i < n; i++) {
	sum = 0;
	mtr = 0;
    for(int j = 0; j < n; j++){
	  sum += a[i][j];
	  c[j] += sum;
	  colmax[j] = max(c[j], colmax[j]);
	  mtr = max(c[j], mtr);
    }
	mtrl = max(mtr, mtrl);
  }
  return mtrl;
}
