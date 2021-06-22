/* Returns the second smallest element of an array */

int _2nd_min (int * a, int n) {
  int m = 0;
  int m2 = 0;
  for(int i = 0; i < n; i++) {
    m2 = min (m2, max (m, a[i]));
    m = min (m, a[i]);
  }
  return m2;
}

/*
  This is the output from the tool, tried two versions
  and both have the same output :

  ($ (min m-$L m-$R)
  (min (min m2-$L m2-$R) (max m-$L m-$R)))

   Join found without auxiliary variable:

   m = min(m-l, m-r)
   m2 = min (min (m2-l, m2-r), max(m-l, m-r))

   in 5.117s.
*/

/* int second_max (int * a, int n) { */
/*   int m = 0; */
/*   int m2 = 0; */

/*   for(int i = 0; i < n; i++) { */
/*     m2 = max (m2, min (m, a[i])); */
/*     m = max (m, a[i]); */
/*   } */
/*   return m2; */
/* } */

/*
   The tool outputs the join :
   ($ (max m-$R m-$L) (max (min m-$R m-$L) (max m2-$L m2-$R))

   Clean join :
   m = max (m-l, m-r);
   m2 = max ( min (m-r, m-l), max (m2-l, m2-r))

 */
