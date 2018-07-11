/*
  This function checks that the ranges of all the lines are overlapping.
*/


_Bool overlap_range(int **A, int m, int n) {
  int low = 0;
  int high = 0;
  int l = 0;
  int h = 0;
  _Bool incl = 1;

  for(int i = 0; i < n; i++) {
	low = 0;
	high = 0;

	for(int j = 0; j < m; j++) {
	  high = max(high, A[i][j]);
	  low = min(low, A[i][j]);
	}

	h = min(h, high);
	l = min(l, low);
	incl = incl && h > l;
  }

  return incl;
}


/*
  Two auxiliaries discovered for the parallel join:
  aux_incl44 = input.high[0]
  aux_incl45 = input.low[0]

  Join :
  low = r.low
  high = r.high
  l = r.l
  h = r.h
  aux_incl44 = l.aux_incl44
  aux_incl45 = l.aux_incl45
  incl = (>= r.aux_incl44 l.h) ? false : ((<= l.aux_incl45 r.l) r.incl && l.incl : false);
*/
