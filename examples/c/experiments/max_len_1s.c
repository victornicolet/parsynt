#include "decl_header.h"

int _max_len_1s (_Bool *a, int n) {
  int cl = 0;
  int ml = 0;
  int c = 0;
  _Bool conj = true;

  for (int i = 0; i < n; i++) {
    cl = a[i] ? cl + 1 : 0;
    ml = max (ml, cl);
    // Auxliiary variables
    conj = conj && a[i];
    c = c + (conj ? 1 : 0);
  }
  return ml + c;
}

/*
  WIth auxliary variables and starting from the functional representation,
  the tool finds the following join :
  conj = conj-l && conj-r
  cl = (! conj-$R) ? cl-r (cl-l + c-r)
  c =  c-l + (! conj-$L) ? 0 : c-r
  ml = max ((+ cl-l c-r), (max (ml-r ml-l))
*/
