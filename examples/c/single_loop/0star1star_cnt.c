_Bool _cnt_0star1star (_Bool *ar, int n) {
  _Bool an = 1;
  _Bool bn = 1;
  int cnt = 0;

  for(int i = 0; i < n; i++) {
    an = (ar [i]) && an;
    bn = ((! ar [i]) || an) && bn;
    cnt = cnt + (ar[i]? 1: -1);
  }

  return cnt;
}
