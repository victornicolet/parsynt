int linear_search_pos(int n, int *a, int x) {
  int pos = -1;
  for(int i = 0;  i < n; i++) {
    if(a[i] == x)
      pos = i;
  }
  return pos;
}

int linear_find(int n, int *a, int x) {
  _Bool f = 0;
  for(int i = 0;  i < n; i++) {
    if(a[i] == x)
      f = 1;
  }
  return f;
}
