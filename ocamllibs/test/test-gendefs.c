#include "stdio.h"


int dummy (int *a1, _Bool x, int a2[10], int n) {
  int sum = 0;

  for (int i = 0; i < n; i++) {
    sum += a1[i] + a2[i];
  }
  return sum;
}

int dumm_bool(int *a, int n) {
  _Bool b = 1;

  for(int i = 0; i < n; i++) {
    b = (a > a[i]);
  }
  return b || 1;
}
