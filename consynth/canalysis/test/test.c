typedef int my_int_arrray[3];

static int a;

int dummy_func(int h) {
  int i;
  int sum = 0;
  for(i = 2; i < h; i++) {
    if (i <= 2) print("2");
    sum += i;
    i += 2;
  }
  return sum;
}

void other_dummy(int n, int *array) {
  int i;
  if (n == 0) {
    return;
  }
  for(i = 0; (i < 10 | i < n); i++) {
    array[i] = i;
    if(i >= 10) {
      array[i] = dummy_func(i);
    }
  }
}

int main (int argc, char **argv) {
  return 0;
}
