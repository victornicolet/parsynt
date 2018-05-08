#include "decl_header.h"

int _min (int *a, int n) {
  int m = _max_int_;
  for(int i = 0; i < n; i++) {
    m = min(m, a[i]);
  }
  return m;
}
