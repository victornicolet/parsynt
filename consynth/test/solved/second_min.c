/* Returns the second smallest element of an array */

int second_smallest (int * a, int n) {
  int m = 0;
  int m2 = 0;
  for(int i = 0; i < n; i++) {
    m = min (m, a[i]);
    m2 = min (m2, max (m, a[i]));
  }
  return m2;
}
