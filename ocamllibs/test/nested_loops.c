int main(int argc, char** argv) {
  int n = 2 << 15;
  int *a;
  a = malloc(n * sizeof(a));
  int i,j, k;
  int m1 = 1;
  int m2 = 0;
  int m3 = 0;
  for(i = 0; i < n; i++){
    for(j = 0; j < n; j++){
      for(k = 0; k < n; k++){
	m3 = m3 * a[j];
      }
      m1 = m3 + m1 * a[j];
    }
    for(k = 0; k < n; k++){
      m3 = m3 * a[j];
    }
    m2 = max(m1, m2);
    m1 = 1;
  }

  return m2;
}
