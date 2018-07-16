/*
   Computes the sum of the box subarray of an array whose
   sum is maximal. A box subarray is a contiguous set of planes
   of the 3D matrix along the outer dimension.
   (example of the maximum segment box of an array).
 */

int _msegbox(int ***a, int m, int n, int o){
  int mbbs = 0;
  int max_box = 0;
  int plane_sum = 0;
  /* Auxiliaries :
	 int sum = 0;
	 int mps = 0;
   */
  for(int i = 0; i < n; i++)
	{
	  plane_sum = 0;
	  for(int j = 0; j < m; j++)
		{
		  for(int k = 0; k < o; k++)
			{
			  bsum += a[i][j][k];
			}
		}
	  /*
		Auxilairies:
		sum = sum + plane_sum;
		mps = max(mps, sum);
	   */
	  mbbs = max(mbbs + plane_sum, 0);
	  max_box = max(mbbs, max_box);
	}
  return max_box;
}

/*
   Join:
   plane_sum = r.plane_sum;
   sum = r.sum + l.sum;
   mps = max(l.mps, l.sum + r.mps)
   mbbs = max(r.mbbs, r.sum + l.mbbs);
   max_box = max(l.max_box, r.max_box, l.mbbs + r.max_top_box)
 */
