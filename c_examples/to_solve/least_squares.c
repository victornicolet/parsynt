int compute_least_squares (int n, int *x, int *y) {
  int SUMx, SUMy, SUMxy, SUMxx;
  SUMx = 0;
  SUMy = 0;
  SUMxx = 0;
  SUMxy = 0;
  for(int i = 0; i < n; i++) {
    SUMx = SUMx + x[i];
    SUMy = SUMy + y[i];
    SUMxy = SUMxy + x[i]*y[i];
    SUMxx = SUMxx + x[i]*x[i];
  }

  return ( SUMx*SUMy - n*SUMxy ) / ( SUMx*SUMx - n*SUMxx );
}
