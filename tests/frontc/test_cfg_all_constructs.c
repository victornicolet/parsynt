static int dummy = 1;

int testfunc(int var, int var1) {
  int a,b,c;
  a = 2;
  b = a + 4;
  c = 10;
  printf("Hello world");
  
  for(a = 0; a < c; a++) {
    printf("ok");
    if( a == 1) 
      b = a + 5;
  }

  switch (a) {
  case 0:
    b = b +3;
  default:
    break;
  }

  return 0;
}
