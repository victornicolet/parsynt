typedef int my_int_arrray[3];


int simple_reduction(int h, int *a) {
  int i;
  int sum = 0;
  for(i = 1; i < h; i++) {
    sum += a[i];
  }
  return sum;
}

int  other_dummy(int n, int array) {
  int i;
  int d;

  if (n == 0) {
    return n;
  }

  for(i = 0; i <= n; i++) {
    d = d * i;
    array = i + d;
  }
  return array;
}

int other_dummy1(int n, int *array) {
  int i,j;
  int sum = 0;
  if (n == 0) {
    return n;
  }
  for(i = 0; (i < 10 | i < n); i++) {
    array[i] = n + i;
    if(i >= 10) {
      array[i] = i + dummy_func(i);
      for(j = 0; (j < 10 | j < n); j++) {
		sum += j;
      }
    }
  }
  return sum;
}

int simple (int *a) {
  int i,j;
  int sum = 0;
  for (i = 3; i < 34; i++) {
    sum += i;
    if (a[i] == 0) sum = 0;
    for(int j = 0; j < 3; j++){
      sum +=j;
    }
    sum++;
  }
  return sum;
}

int main (int argc, char **argv) {
  return 0;
}
