/*
   Maximum top left rectangle (or subarray) example of section 2.4
 */
int _mtlr(int** a, int m, int n) {
  int *c;
  int mtr = 0;
  int mtrl = 0;
  int sum;
  /*
	 int * aux;
   */

  for (int i = 0; i < n; i++) {
	sum = 0;
	mtr = 0;
    for(int j = 0; j < m; j++){
	  sum += a[i][j];
	  c[j] += sum;
	  mtr = max(c[j], mtr);
	  /* Auxiliary:
		 aux[j] = max(aux[j], c[j]);
	  */
    }
	mtrl = max(mtr, mtrl);
  }
  return mtrl;
}

/*
   Join:
   mtrl = l.mtrl;
   mtr = 0
   for j = 0 .. m:
       c[j] = l.c[j] + r.c[j];
	   aux[j] = max(l.aux[j], l.c[j] + r.aux[j])
	   mtr = max(mtr, aux[j]);
   mtrl = max(l.mtrl, mtr);
*/
