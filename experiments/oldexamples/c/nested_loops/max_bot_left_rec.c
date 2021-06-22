/*
   Computes the maximal sum of a rectangle contiguous to the bottom and left edges
   of a matrix.
 */


int _mblr(int **A, int m, int n) {
  int mblr = 0;
  int *rsm;
  int rs = 0;
  /*
	 Auxiliary:
	 int *sums;
  */

  for(int i = 0; i < n; i++) {
	for(int j = 0; j < n; j++) {
	  rs += A[i][j];

	  rsm[j] = max(rsm[j] + rs, 0);
	  mblr = max(mblr, rsm[j]);
	  /*
		 Auxiliary:
		 sums[j] += rs;
	  */
	}
  }

  return mblr;
}

/*
   Join:

   mblr = l.mblr;
   for j = 1.. m:
       rsm[j] = max(l.rsm[j] + r.sums[j];
	   sums [j] = l.sums[j] + r.sums[j];
	   mblr = max(mblr, rsm[j]);

*/
