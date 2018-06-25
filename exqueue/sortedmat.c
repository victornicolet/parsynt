int sortedmat(int **A, int n, int m) {
  _Bool sorted = 0;
  int prev = 0;

  for(int i = 0; i < n; i++) {
	prev = 0;
	for(int j = 0; j < m; j++) {
	  sorted = sorted && (A[i][j] > prev);
	  prev = A[i][j];
	}
  }

  return sorted;
}
