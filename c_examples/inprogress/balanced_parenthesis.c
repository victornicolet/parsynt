#include "stdbool.h"


_Bool balanced_parenthesis (_Bool * string, int n) {
  _Bool is_bal = 1;
  int open = 0;
  int i = 0;
  for(i = 0; i < n; i++) {
    open += string[i] ? 1 : -1;
    is_bal = is_bal && (open > 0);
  }
  return is_bal;
}
