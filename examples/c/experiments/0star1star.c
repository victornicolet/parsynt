_Bool _0star1star (_Bool *ar, int n) {
  _Bool an = 1;
  _Bool bn = 1;

  for(int i = 0; i < n; i++) {
    an = (ar [i]) && an;
    bn = ((! ar [i]) || an) && bn;
  }

  return bn;
}

/* Axuiliary variables discovered :
   a_left = ar[iL]

   Join synthesis in 1,4s
   a_left = a_left-l
   b_left = b_left-l
   an = an-l && an-r
   bn = (bn-r && bn-l) && (b_left-r || an-l)
*/
