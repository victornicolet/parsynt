int positioned_mts (int *a, int n) {
  int pos = -1;
  int mts = 0;

  for (int i = 0; i < n; i++) {
    mts = max (0, mts + a[i]);
    if (mts == 0)
      pos = i + 1;
  }

  return pos;
}


/* Auxiliary variable discovered (sum) :
   aux_0 = aux_0 + a[i]

   Join found with the auxiliary :
   sum = sum-l + sum-r
   mts = max (sum-r + mts-l, mts-r)
   pos = if (sum-r + mts-l > mts-r) pos-l : pos-r
*/
