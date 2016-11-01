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

/*
   Join found without auxiliary variable:

   m = min(m-l, m-r)
   m2 = min (min (m2-l, m2-r), max(m-l, m-r))

   in 5.117s.
*/
