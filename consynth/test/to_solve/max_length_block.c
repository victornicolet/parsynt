int max_length_of_1 (_Bool *a, int n) {
  int cl = 0;
  int ml = 0;
  int c = 0;
  _Bool conj = 1;

  for (int i = 0; i < n; i++) {
    cl = a[i] ? cl + 1 : 0;
    ml = max (ml, cl);
    // Auxliiary variables
    conj = conj && a[i];
    c = c + (conj ? 1 : 0);
  }
  return ml + c;
}
