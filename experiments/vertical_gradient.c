/*
   Check if the matrix is a vertical gradient, that is
   if all the columnds are sorted vertically.
   Possible variation: all the cells in a line should be equal.
*/

int grad1(int **A, int m, int n) {

  _Bool b = 1;
  _Bool bt = 1;

  for(int i = 0; i < n - 1; i++) {
	bt = 1;
	for(int j = 0; j < m - 1; j++) {
	  bt = bt && (A[i+1][j] < A[i][j]);
	}
	b = bt && b;
  }

  return b;
}

/*
   Join:
   b = l.b && r.b
   No auxiliary is needed here because of the direct reference to indexes
   i + 1 and i so there will be an overlapping.
   Another version that would have used an auxiliary and no overlapping of
   of the splitted data would add a prev line that remembers the entire previous
   line.
*/
