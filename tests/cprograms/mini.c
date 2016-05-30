int dummy_func(int h) {
  int i;
  int sum = 0;
  for(i = 0; i < h; i++) {
    sum += i;
  }
  return sum;
}

void other_dummy(int n, int *array) {
  int i;
  for(i = 0; i < n; i++) {
    array[i] = i;
  }
}

int main (int argc, char **argv) {
  return 0;
}
