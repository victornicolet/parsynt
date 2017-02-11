

int count_positives_after_0 (int *a, int n){
  _Bool f = 0;
  int c = 0;
  for (int i = 0; i < n; i++)  {
    c += f && a[i] > 0 ? 1 : 0;
    f = f || a[i] == 0;
  }
  return c;
}
