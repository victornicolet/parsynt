/*
  Checks if the range of the rows are increasing.
  In this problem, the auxliary is discovered for
  the memoryless join.
  It is reused in the parallel join.
*/
_Bool increasing_intervals(int **A, int m, int n) {
  _Bool incr = 1;

  int high = 0;
  int phigh = 0;
  /*
	int in_aux = MAX_INT
  */
  for(int i = 0; i < n; i++) {
	high = MIN_INT;
	for(int j = 0; j < m; j++) {

	  if (A[i][j] <= phigh) {
		incr = 0;
	  }

	  /* in_aux = min(in_aux, A[i][j]); */
	  high = max(high, A[i][j]);
	}
	phigh = high;
  }

  return incr;
}


/*
  Join:
  in_aux = min(l.in_aux, r.in_aux)
  high = r.high
  phigh = r.phigh
  incr = l.incr && (r.in_aux <= l.phigh) false : r.incr
*/
