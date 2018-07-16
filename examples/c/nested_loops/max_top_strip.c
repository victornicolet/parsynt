/*
   Computes the sum of the top subarray of an array whose
   sum is maximal.
   (example of the maximum top strip of an array).
 */

int _mtopstrip(int **a, int m, int n){
  int top_strip_sum = 0;
  int max_top_strip = 0;
  int strip_sum = 0;
  for(int i = 0; i < n; i++)
	{
	  for(int j = 0; j < m; j++)
		{
		  top_strip_sum += a[i][j];
		}
	  max_top_strip = max(max_top_strip, top_strip_sum);
	}
  return max_top_strip;
}


/*
  Join :
  top_strip_sum = r.top_strip_sum + l.top_strip_sum
  max_top_strip = max(l.max_top_strip, r.max_top_strip + l.top_strip_sum)

*/
