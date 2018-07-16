/*
	Returns true if the matrix has a saddle point.
	The matrix has a saddle point if the max of the mins of the columns
	is less than the min of the max of the columns.
 */

_Bool saddle_point(int **a, int n, int m) {
  int* colm;
  int mcols = 0;
  int xrows = 0;
  int rowx = 0;

  colm = malloc(sizeof(colm) * n);

  for(int i = 0; i < n; i++)
	{
	  rowx = MIN_INT;
	  for(int j = 0; j < m; j++)
		{
		  rowx = max(rowx, a[i][j]);
		  colm[j] = min(colm[j], a[i][j]);
		  mcols = max(colm[j], mcols);
		}
	  xrows = min(rowx, xrows);
	}
  return (xrows >= mcols);
}

/*
   Join:
   mcols = l.mcols;
   for j = 0 .. m
       colm[j] = min(l.colm[j], r.colm[j])
	   mcols = max(colm[j], mcols);
   rowx = r.rowx
   xrows = min(l.xrows, r.xrows)

*/
