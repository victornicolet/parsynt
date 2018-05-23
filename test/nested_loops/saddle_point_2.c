_Bool saddle_point_2(int ** a, int n, int m) {
  int *rowx;
  int *rowm;
  int *colm;
  int *colx;
  int mcols = 0;
  int xrows = 0;
  int mrows = 0;
  int xcols = 0;

  for(int i = 0; i< n; i++) {
    for(int j = 0; j < m; j++) {
      rowx[i] = max(rowx[i], a[i][j]); // row max
      rowm[i] = min(rowm[i], a[i][j]); // row min
      colm[j] = min(colm[j], a[i][j]); // col min
      colx[j] = max(colx[j], a[i][j]); // col max
      xcols = max(colm[j], xcols); // max of col min’s
      mcols = min(colx[j], mcols); // min of col max’s
    }
    xrows = min(rowx[i], xrows); // min of row max’s
    mrows = max(rowm[i], mrows); // min of row max’s

  }
  return  (xrows >= mcols) || (mrows <= xcols);
}
