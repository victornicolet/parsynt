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

/*
  New auxiliary variable found :
  aux_0 = a[i0]
  (where i0 is the start index of the loop chunk)

  Join found with auxiliary:

  aux_0 = aux_0-l
  f = f-r
  count = count-r + (f-l && aux0-r) count-l - 1 : count-l

  in 3.067 s.

*/
