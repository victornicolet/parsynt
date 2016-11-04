_Bool alternating_sequence (_Bool *a, int n) {
  _Bool prev = 0;
  _Bool altern = 1;

  for (int i = 0; i < n; i++) {
    altern = altern && (!prev && a[i]) || (prev && !a[i]);
    prev = a[i];
  }
  return altern;
}
