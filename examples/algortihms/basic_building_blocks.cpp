#include <iostream>
#include <math.h>

using namespace std;
int partition (int *x, size_t lo, size_t hi);

// Problem : prefix sum. Writes the prefix sum in the input array.
void prefix_sum (int* x, size_t size) {
  for(int j = 0; j < size; j++) {
    x[j] = x[j] + x[j-1];
  }
}



// Problem : in place integer quicksort
// Sorts the elements in x in place
void integer_quicksort (int *x, size_t lo, size_t hi) {
  if (lo < hi) {
    int p = partition (x, lo, hi);
    integer_quicksort (x, lo, p-1);
    integer_quicksort (x, p, hi);
  }
}

int partition (int *x, size_t lo, size_t hi) {
  int tmp;
  int pivot = x[hi];
  int  i = lo;
  for(int j = lo; j < hi; j++) {
    if(x[j] < pivot){
      tmp = x[i];
      x[i] = x[j];
      x[j] = tmp;
      i ++;
    }
  }
  tmp = x[hi];
  x[hi] = x[i];
  x[i] = tmp;
  return i;
}
  
// Simple matrix multiplication
void mmult_naive (int **A, int **B, int **C, int n, int m) {
  for (int i = 0; i < n; i++) {
    for (int j = 0; j < n; j++) {
      for (int k = 0; k < m; k++) {
	C[i][j] += A[i][k] * B[k][j];
      }
    }
  }
}
 
// Sparse matrix multiplication   
// Compressed Sparse Row
void spmv_csr (int *x, int *row_start, int *col_idx,
	       int *values, int *y, int m, int m) {
  for (int i = 0; i < m; i ++) {
    for (int j = row_start[i]; j < row_start[i+1]) {
      y[i] + values[j] * x[col_idx[j]];
    }
  }
}



int main (int argc, char * argv[]) {
  return 0;
}
