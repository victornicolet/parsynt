/*
  Returns the length of the longest
  balanced substring of a string a.
  Here, a "1" represents an opening bracket
  and a "0" a closing bracket.
 */

int mwbss(_Bool *a, int m, int n) {
  int max_length = 0;
  int offset = 0;
  _Bool balance = 1;

  for(int i = 0; i < n; i++) {
	offset = 0;
	balance = 1;

	for(int j = i; j < n; j++) {

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

/*
  Join:
  offset = r.offset
  balance = r.balance
  max_length = max(r.max_length, l.max_length)
*/
