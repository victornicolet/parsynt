#include "stdio.h"

int sum(int *a, int n) {
  int sum = 0;

  for(int i = 0; i < n; i++) {
    sum += a[i];
  }
  return sum;
}

int length(int *a, int n) {
  int length = 0;
   for(int i = 0; i < n; i++) {
     length++;
  }
   return length;
}


int mps(int* a, int n) {
  int sum = 0, mps = 0;

  for(int i = 0 ; i < n; i++) {
    sum += a[i];
    mps = max(mps, sum);
  }
  return mps + sum;
}


int mts(int* a, int n) {
  int sum = 0, mts = 0;

  for(int i = 0 ; i < n; i++) {
    sum += a[i];
    mts = max(0, mts + a[i]);
  }
  return mts + sum;
}


int mss(int* a, int n) {
  int sum = 0, mts = 0, mps = 0, mss = 0;

  for(int i = 0 ; i < n; i++) {
    sum += a[i];
    mps = max(mps, sum);
    mts = max(0, mts + a[i]);
    mss = max(mss, mts);
  }

  return mts + sum + mps + mss;
}

int line_of_sight(int *a, int n) {
  int amax = 0, visible = 1;

  for(int i = 0; i < n; i++) {
    visible = (amax <= a[i]) ? 1 : 0;
    amax = max(amax, a[i]);
  }
  return visible;
}
