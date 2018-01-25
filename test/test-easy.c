// Simple test : sum reduction

int function (int * array, int n) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    sum += array [i];
  }
  return sum;
}

int second_largest (int *a, int n) {
  int max = 0;
  int smax = 0;
  for (int i = 0; i < n; i++) {
    if (a[i] > max) {
      smax = max;
      max = a[i];
    }
    else if (a[i] > smax) {
      smax = a[i];
    }
  }
  return smax;
}

int majority (int *a, int n) {
  int c = 1;
  int m = a[0];
  for (int i = 1; i < n; i++) {
    if (c == 0) {
      m = a[i];
      c=1;
    }
    else if (a[i] == m)
      { c++; }
    else
      { c--; }
  }
  return m;
}
