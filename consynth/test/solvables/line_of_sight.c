int line_of_sight(int *a, int n) {
  int amax = 0, visible = 1;

  for(int i = 0; i < n; i++) {
    visible = (amax <= a[i]);
    amax = max(amax, a[i]);
  }
  return visible;
}
