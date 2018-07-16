/*
   Computes the maxmimum of the  minimum of each column,
   but through a row-by-row traversal.
*/

int col_maxmin(int **A, int m, int n) {

  int *amin;
  int amaxmin = 0;

  amin = malloc(m * sizeof(amin));

  for(int i = 0; i < n; i++) {
	amaxmin = 0;

	for(int j = 0; j < n; j++) {
	  amin[j] = min (amin[j], A[i][j]);
	  amaxmin = max(amaxmin, amin);
	}
  }
  return amaxmin;
}


/*
  Join:
  for j = 1 .. m:
        amin[j] = min(l.amin[j], r.amin[j]);
		amaxmin = max(amin[j], amaxmin)
*/
