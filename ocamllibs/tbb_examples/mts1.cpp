#include <iostream>
#include <tbb/tbb.h>
#include "mts1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelMts1 {
private:
  int * my_a;
  
public:
  int  my_mts___0;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  int  my_aux_1;
  
  
  ParallelMts1(ParallelMts1& x, split):
    my_a(x.a), my_mts___0(0), my_i_begin_(-1), my_i_end_(-1), my_aux_1(0) {
    }
  
  ParallelMts1(int * a):
    my_a(a), my_mts___0(0), my_i_begin_(-1), my_i_end_(-1), my_aux_1(0) {
    }
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    int * a = my_a;
    int  mts___0 = my_mts___0;
    int  aux_1 = my_aux_1;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       aux_1 = (a[i] + aux_1);
       mts___0 = ((0 > (mts___0 + a[i])) ? 0 : (mts___0 + a[i]));
      
      }
    my_mts___0 = mts___0;
    my_aux_1 = aux_1;
    
    }
  void  join(ParallelMts1& x)
    {
     my_aux_1 = ((x.my_aux_1 - 1) + (my_aux_1 + 1));
     my_mts___0 = ((x.my_mts___0 > (my_mts___0 + x.my_aux_1)) ?
                    x.my_mts___0 : (my_mts___0 + x.my_aux_1));
    }
};

int  TestMts1::parallel_apply() const {
  ParallelMts1 _p_mts_(a);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_mts_);
  return _p_mts_.mts___0;
  
}
int  TestMts1::sequential_apply() const {
  int * a = my_a;
  int  n = my_n;
  int  mts___0 = my_mts___0;
  int  i = my_i;
  int  aux_1 = my_aux_1;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
