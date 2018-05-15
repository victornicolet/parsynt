int _poly (int *coeffs, int n, int x) {
  int res = 0;
  int factor = 1;
  for(int i = 0; i< n; i++) {
    res += factor * coeffs[i];
    factor = x * factor;
  }
  return res;
}

/* Join found without auxiliary variable :
   res = res-l + factor-l * res-r
   factor = factor-l * factor-r

   in
*/
