int explicit_maximum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = ((a[i] > m) ? a[i] : m);
  }
  return m;
}
