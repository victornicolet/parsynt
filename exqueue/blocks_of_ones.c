int block_count(_Bool **a, int n, int m){
  /* assumption: the array only contains boxes */
  int cnt = 0;
  _Bool *prev;

  for(int i = 0; i < n; i++){
	for(int j = 0; j < m; j++){
      if(a[i][j] && ! a[i-1][j] && !prev[j]) cnt++;
	  prev[j] = a[i][j];
	}
  }

  return cnt;
}
