
/* We suppose we have an array of positive integers */
/* Problem : we get the function m -> m instead of the max
   in the body. */

int explicit_maximum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = ((a[i] > m) ? a[i] : m);
  }
  return m;
}

int if_maximum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    if (a[i] > m)
      m = a[i];
  }
  return m;
}

/* Returns the correct join */
int maximum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = max(m, a[i]);
  }
  return m;
}

/* Returns the correct join */
int minimum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = min(m, a[i]);
  }
  return m;
}
