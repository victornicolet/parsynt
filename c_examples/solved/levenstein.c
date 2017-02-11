int levenstein (int *a, int n) {
  int lev_dist = 0;

  for (int i = 0; i < n; i++) {
    lev_dist += ((i % 2) == 0)? a[i]: -a[i];
  }

  return lev_dist;
}
