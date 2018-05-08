#include "decl_header.h"

int _hamming(int *a, int*b, int n) {
  int diff = 0;

  for (int i = 0; i < n; i ++) {
    diff += (!(a[i] == b[i])) ? 0 : 1;
  }

  return diff;
}

/*
  Auxiliary synthesis finds a finite prefix auxliary :

  aux = a[iL]

  And the following join in 1,4s:

  aux = aux-l
  prev = prev-r
  is_sorted = is_sorted-l && is_sorted-r && (prev-l < aux-r)

*/
