#include "stdio.h"


int mts(int* a, int n) {
  int sum = 0, mts = 0;

  for(int i = 0 ; i < n; i++) {
    mts = max(0, mts + a[i]);
  }
  return mts;
}
