/* Match sequences of (10)* */

_Bool alternating_sequence (_Bool *a, int n) {
  _Bool prev = 0;
  _Bool altern = 1;

  for (int i = 0; i < n; i++) {
    altern = altern && (prev ? a[i] : !a[i]);
    prev = a[i];
  }

  return altern;
}

/*
  Join found by the tool, no need for auxiliaries :
  prev = prev-r
  altern = altern-r && (prev-r ? altern-l : false)
*/
