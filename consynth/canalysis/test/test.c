typedef int my_int_arrray[3];


int dummy_func(int h, int *a) {
  int i;
  int sum = 0;
  for(i = 2; i < h; i++) {
    sum += i + a[i];
    i += 2;
    sum = sum - 1;
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
