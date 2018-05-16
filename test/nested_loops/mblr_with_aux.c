
int m_bot_left_rectangle(int** A, int n, int m) {
  int line_sum = 0;
  int* max_rect_col;
  int* sum;
  int mblr = 0; // The max bottom left rectangle

  max_rect_col = malloc(sizeof(max_rect_col) * m);

  for(int i = 0; i < n; i++)
	{
	  line_sum = 0;
	  for(int j = 0; j < m; j++)
		{
		  line_sum += A[i][j];
		  sum[j] += line_sum;
		  max_rect_col[j] = max(max_rect_col[j] + line_sum, 0);
		  mblr = max(mblr, max_rect_col[j]);
		}
	}

  return mblr;
}
