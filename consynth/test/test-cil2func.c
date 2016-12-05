#include "stdio.h"

int main (int argc, char **argv) {
  return 0;
}

int test_simple_loop (int *a, int n) {
  int sum = 0;

  for (int i = 0; i < n; i++) {
    sum += a[i];
    sum++;
  }

  return sum;
}

int test_detect_state (int *a, int n) {
  int not_state = 0;
  int ax = 1;
  int b = 2;
  _Bool c = 0;
  for(int i = 0; i < n; i++) {
    ax = c ? b + a[i] : ax;
    c = ax < 100;
  }
  return not_state + a;
}

int test_merge_ifs (int *a, int n) {
  int b = 0;
  for (int i = 0; i < n; i++) {
    if(a[i] < 0) {
      b = b - a[i];
    } else {
      b = b + a[i];
    }
  }

  return b;
}

int test_nested_loops (int a[100][100], int n, int m) {
  int sum = 0;
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < m; j++) {
      sum += abs(a[i][j] + j);
    }
  }
  return sum;
}

_Bool test_rebuild_and (int a[100], int n) {
  _Bool t = 0;
  for(int i = 0; i < n; i++) {
    t = a[i] && t;
  }
  return t;
}

_Bool test_rebuild_or (int a[100], int n) {
  _Bool t = 0;
  for(int i = 0; i < n; i++) {
    t = a[i] || t;
  }
  return t;
}

int test_balanced_bool (int *a, int n) {
  int wb;
  int diff, min;

  wb = 1;
  diff = 0;
  min = 0;

  for(int i = 0; i < n; i++) {
    if(a[i]) {diff++;} else {diff--;}
    wb = ((wb == 1) & (diff < 0)) ? 1 : 0;
    min = min < diff ? min : diff;
  }
  return wb;
}

int test_and_in_if (_Bool *a, int n) {
  _Bool bal = 1;
  int cnt = 0;


  for (int i = 0; i < n; i++) {
    cnt += (a[i] ? 1 : -1);
    bal = bal && (cnt >= 0);
  }
  return bal;
}

_Bool test_is_sorted (int *a, int n) {
  _Bool is_sorted = 0;
  int prev = 0;

  for (int i = 0; i < n; i ++) {
    is_sorted = is_sorted && (prev < a[i]);
    prev = a[i];
  }

  return is_sorted;
}


int test_drop_while_pos_int (int *a, int n) {
  int pos = 0;
  _Bool first_pos = 1;

  for(int i = 0; i < n; i++) {
    if ((a[i] != 0)) {
      pos = first_pos ? i : pos;
      first_pos = 0;
    }
  }

  return pos;
}

/* Match sequences of (10)* */

_Bool test_alternating_sequence (_Bool *a, int n) {
  _Bool prev = 0;
  _Bool altern = 1;

  for (int i = 0; i < n; i++) {
    altern = altern && (prev ? a[i] : !a[i]);
    prev = a[i];
  }

  return altern;
}

int test_atoi(int *str, int n)
{
    int res = 0;

    for (int i = 0; i < n; i++)
        res = res * 10 + str[i];

    return res;
}

_Bool test_s01 (_Bool *a, int n) {
  _Bool seen = 0;
  _Bool r = 0;

  for (int i = 0; i < n; i++) {
    if (seen && !(a[i]))
      r = 1;
    seen = seen || a[i];
  }

  return r;
}

_Bool test_match_anbn (int *ar, int n, int a, int b) {
  _Bool an = 1;
  _Bool bn = 1;

  for(int i = 0; i < n; i++) {
    an = (ar [i] == a) && an;
    bn = ((ar [i] == b) || an) && bn;
  }

  return bn;
}
