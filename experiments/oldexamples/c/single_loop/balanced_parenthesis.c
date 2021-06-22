_Bool _balanced_parenthesis (_Bool *a, int n) {
  _Bool bal = 1;
  int cnt = 0;
  for (int i = 0; i < n; i++) {
    cnt += (a[i] ? 1 : -1);
    bal = bal && (cnt >= 0);
  }
  return bal;
}

/*
  Discovered one auxiliary variable :
  aux = min (cnt aux)

  Join :
  aux = min (aux-l, (cnt-l + aux-r))
  cnt = cnt-r + cnt-l
  bal = bal-l && (aux-r + cnt-l > 0)

*/
