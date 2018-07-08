int grad2(int **A, int m, int n) {

  _Bool b = 1;
  _Bool bt = 1;

  for(int i = 0; i < n - 1; i++) {
	bt = 1;
	for(int j = 0; j < m - 1; j++) {
	  bt = bt && (A[i+1][j+1] > A[i][j])
		&& (A[i][j+1] > A[i][j])
		&& (A[i+1][j] > A[i][j]);
	}
	b = bt && b;
  }

  return b;
}
