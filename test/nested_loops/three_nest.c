
int three_nest (int *** a, int m, int n, int o) {
  int sum = 0;
  int rect_sum = 0;

  for(int i = 0; i < n; i++){
    rect_sum = 0;
    for(int j = 0; j < m; j++) {
        for(int k = 0; k < o; k++){
	  rect_sum += a[i][j][k];
	}
    }
    sum += rect_sum;
  }

  return sum;
}
