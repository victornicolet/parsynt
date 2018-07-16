float _avg (float *a, int n) {
  float average = 0.0;

  for(int i = 0; i < n; i++) {
    average += (a[i] / n);
  }
  return average;
}
