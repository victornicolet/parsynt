int _mlr(int **A, int m, int n) {
  int rs = 0;
  int mlr = 0;
  int* rects;


  rects = malloc(m * sizeof(rects));

  for(int i = 0; i < n; i++)
	{
	  rs = 0;
	  mlr = 0;
	  for(int j = 0; j < m; j++)
		{
		  rs += A[i][j];
		  rects[j] += rs;
		  mlr = max(mlr, rects[j]);
		}
	}
  return mlr;
}
