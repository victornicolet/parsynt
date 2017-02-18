#include "decl_header.h"

int maximum (int *a, int n) {
  int m = a[0];
  for(int i = 0; i < n; i++) {
    m = max(m, a[i]);
  }
  return m;
}
