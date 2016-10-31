int positioned_mts (int *a, int n) {
  int pos = -1;
  int mts = 0;

  for (int i = 0; i < n; i++) {
    if ((mts + a[i]) > 0)
      pos = i;

    mts = max (0, mts + a[i]);
  }

  return pos;
}
