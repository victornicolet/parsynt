#include <iostream>
#include <tbb/tbb.h>
#include "sum_array1.h.h"

using namespace tbb;

typedef __iterator_type__ long;

class ParallelSum_array1 {
private:
  int * my_a;
  int  my_n;
  
public:
  int  my_sum;
  
  ParallelSum_array1(ParallelSum_array1& x, split)
    my_a(x.a), my_n(x.n), my_sum(0) {}
  ParallelSum_array1(int * a, int  n) my_a(a), my_n(n), my_sum(0) {}
  void  operator()()
    {
    int * a = my_a;
    int  n = my_n;
    int  sum = my_sum;
    int  i = my_i;
    
    if (b < 0 || r.begin() < b)
    b = r.begin(); 
    if (e < 0 || r.end() > e)
    e = r.end();
    
    for (__iterator_type__ i = r.begin(); i!= r.end(); ++i) {
       sum = (sum + a[i]);
      
      }
    my_sum = sum;
    
    }
};

int TestSum_array1::parallel_apply() const {
  ParallelSum_array1 _p_sum_array_(a, n);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_sum_array_);
  return _p_sum_array_.sum;
  
}
int TestSum_array1::sequential_apply() const {
  int * a = my_a;
  int  n = my_n;
  int  sum = my_sum;
  int  i = my_i;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
