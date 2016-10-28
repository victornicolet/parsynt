int polynomial_computation (int *coeffs, int n, int x) {
  int res = 0;
  int factor = 1;
  for(int i = 0; i< n; i++) {
    res += factor * coeffs[i];
    factor = x * factor;
  }
  return res;
}
