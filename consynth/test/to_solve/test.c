int max_length_of_1 (_Bool *a, int n) {
  int cl = 0;
  int ml = 0;

  for (int i = 0; i < n; i++) {
    cl = a[i] ? cl + 1 : 0;
    ml = max (ml, cl);
  }
  return ml + c;
}
