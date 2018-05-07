#include "stdio.h"

int example_minmax(int** a, int n) {
  int minmax = 0;
  int cmax = 0;
  for (int i = 0; i < n; i++) {
	cmax = 0;
    for(int j = 0; j < n; j++){
	  cmax = max(cmax, a[i][j]);
    }
	minmax = min(cmax, minmax);
  }
  return minmax;
}
