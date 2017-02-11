#include "stdbool.h"


/* Again the body is transformed to the identity function */
/* int explicit_minimum (int *a, int n) { */
/*   int m = 0; */
/*   int i; */
/*   for(i = 0; i < n; i++) { */
/*     m = ((a[i] < m) ? a[i] : m); */
/*   } */
/*   return m; */
/* } */

/* int longest_seq_of_ones (_Bool *a, int n) { */
/*   int cur_length = 0; */
/*   int max_length = 0; */

/*   for (int i = 0; i < n; i++) { */
/*     if (a[i]) */
/*       cur_length = cur_length + 1; */
/*     else */
/*       cur_length = 0; */

/*     max_length = max (max_length, cur_length); */
/*   } */

/*   return max_length; */
/* } */

_Bool seen_0_after_1 (_Bool *a, int n) {
  _Bool seen_1 = 0;
  _Bool res = 0;

  /* Additional auxiliary */
  _Bool seen_0 = 0;

  for (int i = 0; i < n; i++) {
    if (a[i])
      seen_1 = 1;
    else
      seen_0 = 1;

    if (seen_1 && !a[i])
      res = 1;
  }

  return res;
}
