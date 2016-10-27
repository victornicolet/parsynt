int mps_with_pos (int *a, int n) {
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
