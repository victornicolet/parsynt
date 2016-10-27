
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

/* Returns the correct join */
int maximum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = max(m, a[i]);
  }
  return m;
}

/* Again the body is transformed to the identity function */
int explicit_minimum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = ((a[i] < m) ? a[i] : m);
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
