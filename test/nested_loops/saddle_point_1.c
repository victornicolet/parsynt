_Bool saddle_point(int **a, int n, int m) {
  int* rowx;
  int* colm;
  int mcols;
  int xrows;

  rowx = malloc(sizeof(rowx) * n);
  colm = malloc(sizeof(colm) * n);

  for(int i = 0; i < n; i++) {
    for(int j = 0; j < m; j++) {
      rowx[i] = max(rowx[i], a[i][j]);
      colm[j] = min(colm[j], a[i][j]);
      mcols = max(colm[j], mcols);
    }
    xrows = min(rowx[i], xrows);
  }
  return (xrows >= mcols);
}
