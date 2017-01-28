_Bool match1001 (int n, _Bool *a) {
  _Bool match00 = 1;
  for(int i = 0; i < n; i++) {
    match00 = ((i == 1) || (i == n-1)) || (match00 && !a[i]);
  }

  return match00 && a[0] && a[n-1];
}
