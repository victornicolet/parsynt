int _dropwhile (int *a, int n) {
  int pos = 0;
  _Bool first_pos = 1;

  for(int i = 0; i < n; i++) {
    if ((a[i] != 0) && first_pos) {
      pos = i;
      first_pos = 0;
    }
  }

  return pos;
}

/*
  Similar join for the integer version, once simplified (the raw output contains
  expressions like (= 0 0) or (! (= (sub1 pos-r) (add1 pos-r)))

  pos =  exit_seq-l ? (max pos-l pos-r) pos-$L
  exit_seq = exit_seq-r && exit_seq-$L

 */
