#include "stdbool.h"

int counting_blocks_of_ones (_Bool * a, int n) {
  int i = 0;
  _Bool f = 0;
  int count = 0;
  for(i =0; i < n; i++) {
    count += (a[i] && !f) ? 1 : 0;
    f = a[i];
  }
  return count;
}
