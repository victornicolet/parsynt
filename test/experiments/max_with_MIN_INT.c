#include "decl_header.h"

int _maximum (int *a, int n) {
  int m = _min_int_;
  for(int i = 0; i < n; i++) {
    m = max(m, a[i]);
  }
  return m;
}
