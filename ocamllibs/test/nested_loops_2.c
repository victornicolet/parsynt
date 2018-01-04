int* comp_array(int** C, int m, int n){
  int i, j;
  for(i = 0; i < n; i++){
    for(j = 0; j < n; j++){
      C[i][j] = C[i-1][j-1] + max(C[i][j-1], C[i-1][j]);
    }
  }
  return C[m-1];
}

/* Dependencies D = (1,0)(0,1)(1,1)

 */
