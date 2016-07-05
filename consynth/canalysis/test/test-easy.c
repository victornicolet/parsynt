// Simple test : sum reduction

int function (int * array, int n) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    sum  += array [i];
  }
  return sum;
}
