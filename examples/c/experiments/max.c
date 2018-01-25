#include "decl_header.h"

int example_max (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = max(m, a[i]);
  }
  return m;
}
