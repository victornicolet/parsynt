/*
   Computes the sum of the bottom subarray (2d) of an array (3d) whose
   sum is maximal.
   (example of the maximum bottom box of a brick).
 */

int _mbotbox(int **a, int m, int n){
  int max_bot_box = 0;
  int box_sum = 0;
  /* Auxiliary : sum = 0; */
  for(int i = 0; i < n; i++)
	{
	  box_sum = 0;
	  for(int j = 0; j < m; j++)
		{
		  box_sum += a[i][j];
		}
	  /*  Auxiliary : sum += box_sum */
	  max_bot_box = max(max_bot_box + box_sum, 0);
	}
  return max_bot_box;
}

/*
   Join:
   box_sum = r.box_sum
   sum = l.sum + r.sum
   max_bot_box = max(r.max_bot_box, r.sum + l.max_bot_box);
 */
