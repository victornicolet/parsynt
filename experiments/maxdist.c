/*
  What is the maximum difference betweem two points of A and B,
  where we assume A is of length n and B is of length m.
*/

int maxdist(int *A, int *B, int n, int m) {
  int md = 0;


  for(int i = 0; i < n; i++) {
	for(int j = 0; j < m; j++) {
	  if (A[i] - B[j] > 0) {
		md = max(md, A[i] - B[j]);
	  } else {
		md = max(md, B[j] - A[i]);
	  }
	}
  }
  return md;
}


/*
   Join :
   md = max(r.md, l.md);
 */
