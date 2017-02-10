_Bool even_len_1s (_Bool *a, int n) {
  _Bool f = 1;
  _Bool g = 0;
  _Bool tf = 1;

  for(int i = 0; i < n; i++) {
    tf = f;
    f = (f && !a[i]) || (!f && !g && a[i]);
    g = !tf;
  }

  return f && g;
}
