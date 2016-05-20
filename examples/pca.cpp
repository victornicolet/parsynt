#include <stdlib.h>
#include <time.h>
#include <math.h>

using namespace std;

float* random_float_vector (int n) {
  float * vec = new float[n];
  srand(time(NULL));
  for(int i = 0; i < n; i++) {
    vec[i] = rand();
  }
  return vec;
}

void incrvec (float *x, float *y, int n) {
  for(int i = 0; i < n; i++)
    x[i] += y[i];
}

void mul_vec_scalar(float *v, float *x, float s, int p){
  for(int i = 0; i < p; i++)
    v[i] = s * x[i];
}

float scalarprod (float *x, float *y, int p) {
  float s = 0;
  for(int i = 0; i < p; i ++) {
    s += x[i] * y[i];
  }
  return s;
}

float norm (float *x, int p) {
  return sqrt(scalarprod(x, x, p));
}

float* iterative_pca (float **x, int c, int p, int n) {
  float* r = random_float_vector(p);
  float* s = new float[p];
  float* v = new float[p];
  for(int i = 0; i < c; i++){
    for (int j = 0; j < n; j++) {
      mul_vec_scalar(v, x[j], scalarprod(x[j], r, p), p);
      incrvec(s, v, p);
    }
    mul_vec_scalar(r, s, 1 / norm(s, p), p);
  }
  delete[] v;
  delete[] s;
  return r;
}


  

int main(int argc, char **argv) {
  return 0;
}
