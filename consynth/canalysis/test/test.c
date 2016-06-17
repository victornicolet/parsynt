typedef int my_int_arrray[3];


int dummy_func(int h, int *a) {
  int i;
  int sum = 0;
  for(i = 2; i < h; i++) {
    if (i <= 2) print("2");
    sum += i + a[i];
    i += 2;
  }
  return sum;
}

void other_dummy(int n, int *array) {
  int i;
  if (n == 0) {
    return;
  }
  for(i = 0; i <= n; i++) {
    array[i] = i;
    if(i >= 10) {
      array[i] = i + dummy_func(i);
    }
  }
}

void other_dummy1(int n, int *array) {
  int i,j;
  int sum = 0;
  if (n == 0) {
    return;
  }
  for(i = 0; (i < 10 | i < n); i++) {
    array[i] = i;
    if(i >= 10) {
      array[i] = i + dummy_func(i);
      for(j = 0; (j < 10 | j < n); j++) {
	sum += j;
      }
    }
  }
}

int main (int argc, char **argv) {
  return 0;
}
