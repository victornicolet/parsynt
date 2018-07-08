int grad1(int **A, int m, int n) {

  _Bool b = 1;

  for(int i = 1; i < n; i++) {
	b = 1;
	for(int j = 1; j < m; j++) {
	  b = b  && (A[i][j] > A[i-1][j]);/* && (A[i][j] > A[i][j-1])); */
	}
  }

  return b;
}
