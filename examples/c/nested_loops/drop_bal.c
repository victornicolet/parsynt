/*
   Count the number of lines that are balanced strings
   of brackets.
   An opening bracket is represented by "0" and a closing
   bracket by "1".
   The synthesis doesn't return a join here, so we only do
   the map. See the paper for the result of the auxiliary
   synthesis for the inner loop.
 */

int drop_bal(_Bool** A, int m, int n) {
  int count = 0;
  int offset = 0;
  int line_offset = 0;
  _Bool bal = 1;

  for(int i = 0; i < n; i++) {

	line_offset = 0;

	for(int j = 0; j < m; j++) {
	  line_offset += A[i][j] ? -1 : 1;

	  bal = bal && ((offset + line_offset) >= 0);
	}

	offset += line_offset;

	if (bal && line_offset >= 0){
	  count++;
	}

  }

  return count;
}
