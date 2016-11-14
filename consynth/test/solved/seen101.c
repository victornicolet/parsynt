_Bool seen_1_0_1 (_Bool *a, int n) {
  _Bool seen = 0;
  _Bool r = 0;

  for (int i = 0; i < n; i++) {
    if (seen && !(a[i]))
      r = 1;
    seen = seen || a[i];
  }

  return r;
}

/*
  Variable discovered (seen0) :
  aux = aux || ! a[i]

  The join discovered is :

  aux = aux-l || aux-r || r-r  --> correct, but I can't eliminate r-r with simple simplifcation  rules
  seen1 = seen1-l || seen1-r || r-l
  r =  (r-l || r-r) || (aux-r && seen1-l)

*/
