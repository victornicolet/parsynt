#include <stdlib.h>
#include <time.h>
#include <math.h>

using namespace std;

#define MAX_VALUE 256


float** init_matrix_random(int, int);
void del_mx(float **, int);
float* random_float_vector(int);

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

float* iterative_pca (float **x, float *r, int c, int p, int n) {
  float* s = new float[p];
  float* v = new float[p];
  for(int i = 0; i < c; i++){
    for (int j = 0; j < n; j++) {
      float sxa = scalarprod(x[j], r, p);
      mul_vec_scalar(v, x[j], sxa, p);
      incrvec(s, v, p);
    }
    mul_vec_scalar(r, s, 1 / norm(s, p), p);
  }
  delete[] v;
  delete[] s;
  return r;
}



int main(int argc, char **argv) {
  int p = 6400;
  int m = 1000;
  float ** mx = init_matrix_random(m, p);
  float *component = random_float_vector(p);

  iterative_pca(mx, component, 20, p, m);

  delete[] component;
  del_mx(mx,m);
}
 
/* Utils */

float** init_matrix_random(int n, int p) {
  float** mx = new float*[n];
  for(int i = 0; i < n; i++)
    mx[i] = random_float_vector(p);
  return mx;
} 

void del_mx (float** mx, int p) {
  for(int i = 0; i < p; i ++) {
    delete mx[i];
  }
  delete[] mx;
}


float* random_float_vector (int n) {
  float * vec = new float[n];
  srand(time(NULL));
  for(int i = 0; i < n; i++) {
    vec[i] = rand() % MAX_VALUE;
  }
  return vec;
}
  
