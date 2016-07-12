#include "stdio.h"

int main (int argc, char **argv) {
  return 0;
}

int test_simple_loop (int *a, int n) {
  int sum = 0;

  for (int i = 0; i < n; i++) {
    sum += a[i];
    sum++;
  }

  return sum;
}

int test_merge_ifs (int *a, int n) {
  int b = 0;
  for (int i = 0; i < n; i++) {
    if(a[i] < 0) {
      b = b - a[i];
    } else {
      b = b + a[i];
    }
  }

  return b;
}

int test_nested_loops (int **a, int n, int m) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < m; j++) {
      sum += a[i][j];
    }
  }
  return sum;
}
