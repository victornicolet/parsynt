/*
   Computes the sum of the segment subarray of an array whose
   sum is maximal. A segment subarray is a contiguous set of lines
   of the matrix.
   (example of the maximum segment strip of an array).
 */

int _msegstrip(int **a, int m, int n){
  int max_bot_strip = 0;
  int max_strip = 0;
  int strip_sum = 0;
  /* Auxiliaries :
	 int sum = 0;
	 int mps = 0;
   */
  for(int i = 0; i < n; i++)
	{
	  strip_sum = 0;
	  for(int j = 0; j < m; j++)
		{
		  strip_sum += a[i][j];
		}
	  /*
		 Auxilairies:
		 sum = sum + strip_sum;
		 mps = max(mps, sum);
	   */
	  max_bot_strip = max(max_bot_strip + strip_sum, 0);
	  max_strip = max(max_bot_strip, max_strip);
	}
  return max_strip;
}


/*
   Join:
   strip_sum = r.strip_sum;
   sum = r.sum + l.sum;
   mps = max(l.mps, l.sum + r.mps)
   max_bot_strip = max(r.max_bot_strip, r.sum + l.max_bot_strip);
   max_strip = max(l.max_strip, r.max_strip, l.max_bot_strip + r.max_top_strip)
 */
