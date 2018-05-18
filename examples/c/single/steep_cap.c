

int capacity(int* a, int n) {
  int c = 0;
  int sum = 0;
  for(int i =0; i< n; i++){
	sum += a[i];
	c = min(c - a[i], a[i]);
  }
  return c;
}
