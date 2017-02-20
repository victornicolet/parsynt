static const int __MIN_INT_ = -9999;

_Bool example_is_sorted (int *a, int n) {
  _Bool iss = 1;
  int prev = _min_int_;

  for (int i = 0; i < n; i ++) {
    iss = iss && (prev < a[i]);
    prev = a[i];
  }

  return iss;
}

/*
  Auxiliary synthesis finds a finite prefix auxiliary :

  aux = a[iL]

  And the following join:

  aux = aux-l
  prev = prev-r
  is_sorted = is_sorted-l && is_sorted-r && (prev-l < aux-r)

*/