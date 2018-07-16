int _mps_p (int *a, int n) {
  int mps = 0;
  int pos = 0;
  int sum = 0;
  for(int i = 0; i < n; i ++) {
    sum += a[i];
    if (sum > mps)
      pos = i;
    mps = max (mps, sum);
  }
  return pos;
}


/* Join found without auxiliary variable generation :

   mps = max (mps-l, mps-r + sum-l)
   pos = ( mps-r + sum-$L > mps-r) ? pos-r : pos-l
   sum = sum-l + sum-r

   in 76.993 s.
*/
