int _mode(int **a, int n, int m) {
  /* Inner loop variables */
  int cnt = 0; /* Counting variable for the inner loop */
  int elt = 0; /* The element we are counting in the inner loop */
  /* Outer loop variables */
  int mode = 0; /* The mode of the sequence so far */
  int max_cnt = 0; /* The count of the mode so far */

  for(int i = 0; i < n; i++){
    /* At iteration i count how many times a[i] appears */
    elt = a[i];
    cnt = 0;

    for(int j = 0; j < n; j++){ /* j < i is also correct */
      if(a[j] == elt) {
	cnt++;
      }
    }

    if(cnt > max_cnt){
      max_cnt = cnt;
      mode = elt;
    }
  }

  return mode;
}
