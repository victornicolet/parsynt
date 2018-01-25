int special_mts (int *a, int n, int b){
  int mts = -1;

  for (int i = 0; i < n; i++) {
    if (a[b] > 0 )
      {
	mts = max(mts + a[i], 0);
      }
  }
  return mts;
}
