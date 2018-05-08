#include "stdio.h"


int _mss (int* a, int n) {
  int mts = 0;
  int sum = 0;
  int mps = 0;
  int mss = 0;

  for(int i = 0; i < n; i++) {
    mss = max (mss, mts + a[i]);
    mts = max (0, mts + a[i]);
  }
  return mss;
}
