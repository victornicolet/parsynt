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

int longest_seq_of_zeros (_Bool *a, int n) {
  int cur_length = 0;
  int max_length = 0;
  _Bool in_seq = 1;

  for (int i = 0; i < n; i++) {

    if (in_seq && !a[i])
      cur_length += 1;
    else
      cur_length = 0;

    in_seq = a[i];
    max_length = max (max_length, cur_length);
  }

  return max_length;
}
