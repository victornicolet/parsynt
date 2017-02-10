int div3 (_Bool *a, int n) {
  int r = 0;
  for (int i =0; i < n; i++){
    r = (r + (a[i] ? 1:0)) % 3;
  }

  return r;
}
