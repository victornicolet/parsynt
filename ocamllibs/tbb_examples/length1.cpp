#include <iostream>
#include <tbb/tbb.h>
#include "length1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelLength1 {
private:
  
public:
  int  my_length___0;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  
  
  ParallelLength1(ParallelLength1& x, split):
    my_length___0(0), my_i_begin_(-1), my_i_end_(-1) {}
  
  ParallelLength1(): my_length___0(0), my_i_begin_(-1), my_i_end_(-1) {}
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    int  length___0 = my_length___0;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       length___0 = (length___0 + 1);
      
      }
    my_length___0 = length___0;
    
    }
  void  join(ParallelLength1& x)
    {
     my_length___0 = ((my_length___0 + 1) + (x.my_length___0 - 1));
    }
};

int  TestLength1::parallel_apply() const {
  ParallelLength1 _p_length_();
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_length_);
  return _p_length_.length___0;
  
}
int  TestLength1::sequential_apply() const {
  int  n = my_n;
  int  length___0 = my_length___0;
  int  i = my_i;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
