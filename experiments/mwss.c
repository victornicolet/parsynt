int mwbss(_Bool *a, int m, int n) {
  int max_length = 0;
  int offset = 0;
  _Bool balance = 1;

  for(int i = 0; i < n; i++) {
	offset = 0;
	balance = 1;

	for(int j = 0; j < n; j++) {

	  offset += a[j] ? 1 : -1;

	  if (offset == 0 && balance) {
		max_length = max(max_length, j - i + 1);
	  }
	  if (offset <= 0 ) {
		balance = 0;
	  }
	}
  }

  return max_length;
}
