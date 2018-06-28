int _mblr(int **a, int n, int m) {
  int mblr = 0;
  int *C;
  int sum;

  for(int i = 0; i < n; i++) {
	sum = 0;
	for(int j = 0; j < m; j++) {
	  sum += a[i][j];
	  C[j] = max(C[j] + sum, 0);
	  mblr = max(mblr, C[j]);
	}
  }

  return mblr;
}
