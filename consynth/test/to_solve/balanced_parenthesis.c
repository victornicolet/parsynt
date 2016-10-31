_Bool balanced_string (_Bool *a, int n) {
  _Bool bal = 1;
  int count = 0;
  for (int i = 0; i < n; i++) {
    count += (a[i] ? 1 : -1);
    bal = bal && (count >= 0);
  }
  return bal;
}
