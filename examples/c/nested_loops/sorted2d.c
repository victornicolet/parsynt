/*
   Return if a matrix is sorted (reading line by line).
 */

_Bool is_sorted(int **A, int n, int m) {
  int prev = __MIN_INT_;
  _Bool iss = 0;

  for(int i = 0; i < n; i++) {
	for(int j = 0; j < m; j++) {
	  iss = iss && (A[i][j] > prev);
	  prev= A[i][j];
	}
  }

  return iss;
}


/*
   Auxiliary required (first cell of the chunk);
   aux = A[i0][0]
   Join:
   iss = l.iss & r.iss & r.prev > l.aux
   prev = r.prev
   aux = l.aux
*/
