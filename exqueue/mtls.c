int _mtls(int **a, int m, int n) {
  int maxsq = 0;
  int* colsum;
  int boxsum = 0;

  for (int i = 0; i < n; i++) {

    boxsum = 0;

    for (int j = 0; j < m; j++) {

      colsum[j] += a[i][j];

      if (j <= i) {
	boxsum += colsum[j];
      }
    }

    maxsq = max(maxsq, boxsum);
  }

  return maxsq;
}
