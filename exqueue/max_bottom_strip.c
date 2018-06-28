int _mbotstrip(int **a, int m, int n){
  int max_bot_strip = 0;
  int strip_sum = 0;
  for(int i = 0; i < n; i++)
	{
	  strip_sum = 0;
	  for(int j = 0; j < m; j++)
		{
		  strip_sum += a[i][j];
		}
	  max_bot_strip = max(max_bot_strip + strip_sum, 0);
	}
  return max_bot_strip;
}
