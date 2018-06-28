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
