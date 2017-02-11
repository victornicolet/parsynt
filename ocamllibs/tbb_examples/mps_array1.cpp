#include <iostream>
#include <tbb/tbb.h>
#include "mps_array1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelMps_array1 {
private:
  int * my_a;
  
public:
  int  my_sum;
  int  my_mps;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  
  
  ParallelMps_array1(ParallelMps_array1& x, split):
    my_a(x.a), my_sum(0), my_mps(0), my_i_begin_(-1), my_i_end_(-1) {
    }
  
  ParallelMps_array1(int * a):
    my_a(a), my_sum(0), my_mps(0), my_i_begin_(-1), my_i_end_(-1) {}
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    int * a = my_a;
    int  sum = my_sum;
    int  mps = my_mps;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       mps = (((sum + a[i]) > mps) ? (sum + a[i]) : mps);
       sum = (sum + a[i]);
      
      }
    my_sum = sum;
    my_mps = mps;
    
    }
  void  join(ParallelMps_array1& x)
    {
     my_mps = ((((-3940 + my_mps) + 3940) > (x.my_mps + my_sum)) ?
                ((-3940 + my_mps) + 3940) : (x.my_mps + my_sum));
     my_sum = (my_sum + x.my_sum);
    }
};

int  TestMps_array1::parallel_apply() const {
  ParallelMps_array1 _p_mps_array_(a);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_mps_array_);
  return _p_mps_array_.mps;
  
}
int  TestMps_array1::sequential_apply() const {
  int * a = my_a;
  int  n = my_n;
  int  sum = my_sum;
  int  mps = my_mps;
  int  i = my_i;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
