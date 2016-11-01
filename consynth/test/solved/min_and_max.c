
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

/* Join is : (m-L > -7885) ? max (m-l,  m-r) :  max(m-l, m-r)
 ---> Simplifies to :  max (m-l, m-r) */


int if_maximum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    if (a[i] > m)
      m = a[i];
  }
  return m;
}


/* Join is : (m-L > -7885) ? max (m-l,  m-r) :  max(m-l, m-r)
 ---> Simplifies to :  max (m-l, m-r) */


int maximum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = max(m, a[i]);
  }
  return m;
}


/* Join is : max (m-l, m-r) */


/* Returns the correct join */
int minimum (int *a, int n) {
  int m = 0;
  for(int i = 0; i < n; i++) {
    m = min(m, a[i]);
  }
  return m;
}


/* Join is : min (m-l, m-r) */
