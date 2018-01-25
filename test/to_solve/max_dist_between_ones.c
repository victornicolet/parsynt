#include "decl_header.h"

int max_dist_btw_ones (_Bool * a, int n) {
  int max_d = 0;
  int cur_l = 0;
  /* Auxiliary variables */
  _Bool conj = true;
  int pre_l = 0;

  for (int i = 0; i < n; i++) {
    if (a[i]) {
      max_d = max (max_d, cur_l);
      cur_l = 0;
    } else {
      cur_l += 1;
    }
    conj = conj && a[i];
    pre_l = pre_l + (conj ? 1 : 0);
  }

  return max_d + conj ? pre_l : 0;
}
