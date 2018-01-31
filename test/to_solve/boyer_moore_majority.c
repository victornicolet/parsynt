int majority (int *a, int n){

  int cnt = 0;
  int i = 0;
  int m = a[0];

  for(i = 0; i < n; i++){
    if(cnt == 0) {
      m = a[i];
      cnt = 1;
    } else {
      if(m == a[i]) {
	cnt ++;
      } else {
	cnt --;
      }
    }
  }

  return m;
}
