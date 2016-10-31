/* A limited line-of-sight implementation :
   - We suppose the array has only positive elements.
   - There is not notion of angle or whatsoever : a bulding
   is visible is there is no greater building seen before, from
   left to right.
   - We add the auxiliary prev in this version : this should be discovered by
   the variable discovery algorithm */

_Bool line_of_sight(int *a, int n) {
  int amax = 0;
  _Bool visible = 1;

  for(int i = 0; i < n; i++) {
    visible = (amax <= a[i]);
    amax = max(amax, a[i]);
  }
  return visible;
}
