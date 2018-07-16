/* Computes the maximum of the minimums of each
   line. Only scalars in this simple example.
*/

int maxmin(int **A, int m, int n) {
  int amin = 0;
  int amaxmin = 0;

  for(int i = 0; i < n; i++) {
	amin = 0;
	for(int j = 0; j < n; j++) {
	  amin = min (amin, A[i][j]);
	}
	amaxmin = max(amaxmin, amin);
  }
  return amaxmin;
}


/*
  Join:
  amin = r.amin
  amaxmin = max(l.amaxmin, r.amaxmin)
*/
