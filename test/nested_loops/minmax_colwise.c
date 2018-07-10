int minimax_col(int** A, int n, int m)
{
  int* mins;
  int cmax = 0;

  for(int i = 0; i < n; i++) {
	  for(int j = 0; j < m; j++) {
		mins[j] = min(mins[j], A[i][j]);
		cmax = max(mins[j], cmax);
	  }
  }
  return cmax;
}
