#include "stdio.h"

typedef int bool;
#define true 1
#deifne false 0

int dummy (int *a1, _Bool x, int a2[10], int n) {
  int b = 0;

  for (int i = 0; i < n; i++) {
    if((a1[i] < 0) && x) {
      b = b - a1[i] + a2[i % 10];
    } else {
      b = b + a1[i] + a2[i % 5];
    }
  }
  return b;
}
