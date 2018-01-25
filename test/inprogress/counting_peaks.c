#include "stdbool.h"

/** Assumptions :
    - the input array contains only positive integers. Otherwise we can
    normalize it by adding the opposite of the minimum to every element.
    This doesn't change the results of couting peaks. */

int counting_peaks (int *a, int n) {
  int cnt;
  _Bool slope = 1;
  int prev = 0;
  int i;
  for (i = 0; i < n; i++) {
    cnt += (slope && (a[i] < prev)) ? 0 : 1;
    slope = a[i] > prev;
    prev = a[i];
  }
  return cnt;
}
