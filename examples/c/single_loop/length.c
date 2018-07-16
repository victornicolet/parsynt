int _length (int *a, int n) {
  int length = 0;

  for (int i = 0; i < n; i++) {
    length++;
  }
  return length;
}

/*
  Join found without auxiliary variable:

  length = length-l + length-r

  in 1.554 s
*/
