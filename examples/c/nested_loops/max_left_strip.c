/* Computes the sum of the rectangle contiguous to the
   left, top and bottom edges of the array whose sum
   is maximal.

   The maximum left subarray sum.
*/

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


/*
   Join:
   rs = r.rs
   for j = 1 .. m:
       rects[j] = l.rects[j] + r.rects[j]
	   mlr = max(mlr, rects[j]);
*/
