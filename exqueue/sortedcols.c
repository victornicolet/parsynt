int sortedcols (int **A, int m, int n) {
  _Bool  *scols;
  int * prevs;

  for(int i = 0; i < n; i++) {
	for(int j = 0; j < m; j++) {
	  scols[j] = scols[j] && prevs[j] > A[i][j];
	  prevs[j] = A[i][j];
	}
  }
  return scols;
}
