// Simple test : sum reduction

int function (int * array, int n) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    sum  += array [i];
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
