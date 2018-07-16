#include "decl_header.h"

int _max (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    if (m < a[i]) {
      m = a[i];
    }
  }
  return m;
}
