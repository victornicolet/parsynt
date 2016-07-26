#include "stdio.h"

typedef int bool;
#define true 1
#deifne false 0

int dummy (int *a1, _Bool x, int a2[10], int n) {
  int sum = 0;

  for (int i = 0; i < n; i++) {
    sum += a1[i] + a2[i];
  }
  return sum;
}
