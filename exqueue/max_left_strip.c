

int _mls(int **A, int m, int n) {
  int mls = 0;
  int lsum = 0;
  int* lrects;

  for(int i = 0; i < n; i++)
	{
	  lsum = 0;
	  mls = 0;
	  for(int j = 0; j < m; j++)
		{
		  lsum += A[i][j];
		  lrects[j] += lsum;
		  mls = max(lrects[j], mls);
		}
	}
  return mls;
}
