#include <iostream>
#include <tbb/tbb.h>
#include "diff1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelDiff1 {
private:
  int * my_a;
  int * my_b;
  
public:
  int  my_diff___0;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  
  
  ParallelDiff1(ParallelDiff1& x, split):
    my_a(x.a), my_b(x.b), my_diff___0(0), my_i_begin_(-1), my_i_end_(-1) {
    }
  
  ParallelDiff1(int * a, int * b):
    my_a(a), my_b(b), my_diff___0(0), my_i_begin_(-1), my_i_end_(-1) {
    }
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    int * a = my_a;
    int * b = my_b;
    int  diff___0 = my_diff___0;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       diff___0 = (diff___0 + (not (a[i] = b[i])]@ ? 0 : 1));  }
      my_diff___0 = diff___0;
      
    }
    void  join(ParallelDiff1& x)
      {
       my_diff___0 = ((my_diff___0 - 1) + (#t ? (x.my_diff___0 + 1) :
                                            (6 - 1)));
      }
  };

int  TestDiff1::parallel_apply() const {
  ParallelDiff1 _p_diff_(a, b);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_diff_);
  return _p_diff_.diff___0;
  
}
int  TestDiff1::sequential_apply() const {
  int * a = my_a;
  int * b = my_b;
  int  n = my_n;
  int  diff___0 = my_diff___0;
  int  i = my_i;
  int  tmp = my_tmp;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
