_Bool match_anbn (int *ar, int n, int a, int b) {
  _Bool an = 1;
  _Bool bn = 1;

  for(int i = 0; i < n; i++) {
    an = (ar [i] == a) && an;
    bn = ((ar [i] == b) || an) && bn;
  }

  return bn;
}

/* Axuiliary variables discovered :
   a_left = ar[iL] == a
   b_left = ar[iR] == b

   Join synthesis in 1,4s
   a_left = a_left-l
   b_left = b_left-l
   an = an-l && an-r
   bn = (bn-r && bn-l) && (b_left-r || an-l)
*/
