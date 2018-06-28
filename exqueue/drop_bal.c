int drop_count(_Bool** A, int m, int n) {
  int count = 0;
  int offset = 0;
  int line_offset = 0;
  _Bool bal = true;

  for(int i = 0; i < n; i++) {
	line_offset = 0;
	for(int j = 0; j < m; j++) {
	  line_offset += A[i][j] ? -1 : 1;
	  bal = bal && ((offset + line_offset) < 0);
	}
	offset += line_offset;
	if (bal && line_offset > 0){
	  count++;
	}
  }

  return count;
}
