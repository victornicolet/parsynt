#include "tbb/tbb.h"
#include <stdlib.h>
#include <time.h>
#include <math.h>

using namespace std;
using namespace tbb;

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

class ApplyPCA {
  float *m_s;
  float *m_r;
  float **m_matrix;
  int m_n,m_p;
public:
  void operator() (blocked_range<int> &r) {
    float* l_v = new float[m_p];
    for(int i = r.begin(); i != r.end(); i++) {
      mul_vec_scalar(l_v, m_matrix[i], scalarprod(m_matrix[i], m_r, m_p), m_p);
      incrvec(m_s, l_v, m_p);
    }
    delete[] l_v;
  }

  void join(ApplyPCA &x) {
    incrvec(m_s, x.m_s, m_p);
    delete[] x.m_s;
  }
  
  ApplyPCA(ApplyPCA &x, split):
    m_matrix(x.m_matrix), m_n(x.m_n), m_p(x.m_p), m_r(x.m_r)
  {
    m_s = new float[m_p];
    for(int i = 0; i < m_p; i++) {
      m_s = 0;
    }
  }

  ApplyPCA(float **x, float *r, int n, int p) :
    m_matrix(x), m_p(p), m_n(n), m_r(r)
  {
    m_s = new float[m_p];
    for(int i = 0; i < m_p; i++) {
      m_s = 0;
    }
  }
};


int main (int argc, char **argv) {
  return 0;
}



