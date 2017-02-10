int div3bis (_Bool *a, int n) {
  _Bool f=false;
  _Bool g=false;
  for (int i = 0; i < n; i++) {
    if (a[i]) {
      g = (!g || !f);
      f = (!g )? !f : f;
    }
  }
  return f;
}
