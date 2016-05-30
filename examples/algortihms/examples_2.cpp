#include <cstdio>
#include <stdlib.h>
#include <iostream>
#include <math.h>
#include <time.h>

using namespace std;

/* 
   Random permutation 
*/
int* rpermute(int n) {
  int * a = new int[n];
  int k;
  for (k = 0; k < n; k++)
    a[k] = k;
  for (k = n-1; k > 0; k--) {
    int j = rand() % (k+1);
    int temp = a[j];
    a[j] = a[k];
    a[k] = temp;
  }
  return a;
}
 
/* 
   Remove duplicates
*/
int* remove_duplicates(int* array, int size, int (*hash)(int)) {
  int * hashed = new int[size];
  int nu_size = size;
  for(int i=0; i < size; i++){
    if(hashed[hash(i)] == -1) {
      nu_size--;
    }
  }
}
    

/*
  List contraction.
  - A list is represented by an array L where L[i]
  stores the predecessor and the successor of node
  i.
  - The algorithm contracts the list into a single
  node, combining the values with an operator.
*/




int main (int argc, char **argv) {
  srand(time(NULL));
  int* p16 = rpermute(16);
  for (int k = 0; k < 16; k++) {
    cout << p16[k] << " " ;
  }
  delete[] p16;
  cout << endl;
}
