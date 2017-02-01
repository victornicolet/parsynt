#include <iostream>
#include <tbb/tbb.h>
#include "sum_array1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelSum_array1 {
private:
  int * my_a;
  
public:
  int  my_sum;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  
  
  ParallelSum_array1(ParallelSum_array1& x, split):
    my_a(x.a), my_sum(0), my_i_begin_(-1), my_i_end_(-1) {}
  
  ParallelSum_array1(int * a):
    my_a(a), my_sum(0), my_i_begin_(-1), my_i_end_(-1) {}
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    int * a = my_a;
    int  sum = my_sum;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       sum = (sum + a[i]);
      
      }
    my_sum = sum;
    
    }
  void  join(ParallelSum_array1& x) {  my_sum = ((x.my_sum + 0) + my_sum); }
};

int  TestSum_array1::parallel_apply() const {
  ParallelSum_array1 _p_sum_array_(a);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_sum_array_);
  return _p_sum_array_.sum;
  
}
int  TestSum_array1::sequential_apply() const {
  int * a = my_a;
  int  n = my_n;
  int  sum = my_sum;
  int  i = my_i;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
