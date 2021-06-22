int _mode(int *a, int n, int m) {

  int cnt = 0; /* Counting variable for the inner loop */
  int elt = 0; /* The element we are counting in the inner loop */

  int mode = 0; /* The mode of the sequence so far */
  int max_cnt = MIN_INT; /* The count of the mode so far */

  for(int i = 0; i < n; i++){

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
/* Join
   cnt = r.cnt
   elt = r.elt
   max_cnt = max(r.max_cnt, l.max_cnt)
   mode =  (r.max_cnt > l.max_cnt) ? l.mode : r.mode
*/
