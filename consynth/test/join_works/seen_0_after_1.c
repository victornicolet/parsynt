_Bool seen_0_after_1 (_Bool *a, int n) {
  _Bool seen0 = 0;
  _Bool seen1 = 0;
  _Bool r = 0;

  for (int i = 0; i < n; i++) {
    if (seen1 && !(a[i]))
      r = 1;
    seen1 = seen1 || a[i];
    seen0 = seen0 || (! a[i]);
  }
  seen1 = seen0;

  /* Force CIL to keep all variables */
  return r || seen1 || seen0;
}

/*
  First version with the auxiliary variable, the join discovered is
  seen0 = seen0-l || seen0-r
  seen1 = seen1-l || seen1-r
  r = seen1-r || true ???

  We don't get a good answer ...
*/
