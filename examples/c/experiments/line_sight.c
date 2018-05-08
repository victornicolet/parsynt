/* A limited line-of-sight implementation :
   - We suppose the array has only positive elements.
   - There is not notion of angle or whatsoever : a bulding
   is visible is there is no greater building seen before, from
   left to right.
   - To recompute the "visible" variable in the join, we need to
   know the height of the last building, and compare it to the
   updated max.
*/

_Bool _line_sight (int *a, int n) {
  int amax = 0;
  _Bool visible = 1;

  for(int i = 0; i < n; i++) {
    visible = (amax <= a[i]);
    amax = max (amax, a[i]);
  }
  return visible;
}

/*
  Auxliary variable discovered (remember last cell):
  aux = a[i]

  Corresponding join :

  aux = aux-r;
  amax = max (amax-r, amax-l)
  visible = max (amax-l, amax-r) <= aux-r

  In 7.872 s.
*/
