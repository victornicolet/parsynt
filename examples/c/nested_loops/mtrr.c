/*
   Maximum top right rectangle.
   Computes the maximum top right rectangle sum in mtrr.
*/

int _mtrr(int** a, int* c, int n, int m) {
  int mtr = 0;
  int mtrr = 0;
  /*
	 Auxilary:
	 int acc_aux;
	 int *aux;
	 int j2;
   */
  for (int i = 0; i < n; i++) {
	mtr = 0;
	/*
	   acc_aux = 0;
	 */
    for(int j = 0; j < m; j++){
	  c[j] += a[i][j];
	  mtr = max(mtr + c[j], 0);
	  /*
		 Auxilary is leftwards:
		 j2 = m - j - 1;
		 acc_aux += c[j2] + A[i][j2];
		 aux[j2] = max(acc_aux, aux[j2]);
	  */
    }
	mtrr = max(mtr, mtrr);
  }
  return mtrr;
}

/*
  Join:
  acc_aux = 0;
  mtr = 0;
  for j = 0 .. m:
      c[j] = l.c[j] + r.c[j];
      j2 = m - j - 1
      acc_aux += l.c[j];
      aux[j2] = max(acc_aux + r.aux[j2], l.aux[j2])
      mtr = max(aux[j2], mtr)
  mtrr = max(l.mtrr, mtr)
*/
