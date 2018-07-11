/*
   Computes the maximum top left square of a matrix.
   If m > n, then the square degenerates to a
   rectangle (condition j <= i).
 */

int _mtls(int **a, int m, int n) {
  int* colsum;
  /* int* rec; */
  int rs = 0;
  int maxsq = 0;

  for (int i = 0; i < n; i++) {
	rs = 0;
    for (int j = 0; j < m; j++) {
	  rs += a[i][j];
      colsum[j] += rs;
	  /* if (i == j) { */
	  /* 	rec[j] = colsum[j]; */
	  /* } */
    }

    maxsq = max(maxsq, colsum[i]);
  }

  return maxsq;
}

/*
  Auxiliary : rec
   Join:
   for j = 0 .. m-1:
       colsum[j] = l.colsum[j] + r.colsum[j]
	   rec[j] = r.rec[j]
	   maxsq = max(maxsq,
*/
