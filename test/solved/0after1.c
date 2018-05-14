_Bool _0after1 (_Bool *a, int n) {
  _Bool seen1 = 0;
  _Bool res = 0;

  for (int i = 0; i < n; i++) {
    if (seen1 && !(a[i]))
      res = 1;
    seen1 = seen1 || a[i];
  }

  return res;
}

/*
  Variable discovered (seen0) :
  aux = aux || ! a[i]

  The join discovered is :

  aux = aux-l || aux-r || r-r  --> correct, but I can't eliminate r-r with simple simplifcation  rules
  seen1 = seen1-l || seen1-r || r-l
  r =  (r-l || r-r) || (aux-r && seen1-l)

*/
