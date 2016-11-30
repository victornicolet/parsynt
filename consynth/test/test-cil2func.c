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

/* int test_nested_loops (int a[100][100], int n, int m) { */
/*   int sum = 0; */
/*   for (int i = 0; i < n; i++) { */
/*     for (int j = 0; j < m; j++) { */
/*       sum += abs(a[i][j] + j); */
/*     } */
/*   } */
/*   return sum; */
/* } */

/* int test_balanced_bool (int *a, int n) { */
/*   int wb; */
/*   int diff, min; */

/*   wb = 1; */
/*   diff = 0; */
/*   min = 0; */

/*   for(int i = 0; i < n; i++) { */
/*     if(a[i]) {diff++;} else {diff--;} */
/*     wb = ((wb == 1) & (diff < 0)) ? 1 : 0; */
/*     min = min < diff ? min : diff; */
/*   } */
/*   return wb; */
/* } */

int test_and_in_if (_Bool *a, int n) {
  _Bool bal = 1;
  int cnt = 0;


  for (int i = 0; i < n; i++) {
    cnt += (a[i] ? 1 : -1);
    bal = bal && (cnt >= 0);
  }
  return bal;
}

_Bool is_sorted (int *a, int n) {
  _Bool is_sorted = 0;
  int prev = 0;

  for (int i = 0; i < n; i ++) {
    is_sorted = is_sorted && (prev < a[i]);
    prev = a[i];
  }

  return is_sorted;
}
