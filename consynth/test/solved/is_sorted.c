#include "decl_header.h"

_Bool is_sorted (int *a, int n) {
  _Bool is_sorted = 1;
  int prev = _min_int_;

  for (int i = 0; i < n; i ++) {
    is_sorted = is_sorted && (prev < a[i]);
    prev = a[i];
  }

  return is_sorted;
}

/*
  Auxiliary synthesis finds a finite prefix auxliary :

  aux = a[iL]

  And the following join:

  aux = aux-l
  prev = prev-r
  is_sorted = is_sorted-l && is_sorted-r && (prev-l < aux-r)

*/
