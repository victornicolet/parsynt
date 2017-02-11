#include <iostream>
#include <tbb/tbb.h>
#include "is_sorted1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelIs_sorted1 {
private:
  int * my_a;
  
public:
  _Bool  my_iss;
  int  my_prev;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  int  my_aux_0;
  
  
  ParallelIs_sorted1(ParallelIs_sorted1& x, split):
    my_a(x.a), my_iss(#t), my_prev(-inf.0), my_i_begin_(-1), my_i_end_(-1), my_aux_0(0) {
    }
  
  ParallelIs_sorted1(int * a):
    my_a(a), my_iss(#t), my_prev(-inf.0), my_i_begin_(-1), my_i_end_(-1), my_aux_0(0) {
    }
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    int * a = my_a;
    _Bool  iss = my_iss;
    int  prev = my_prev;
    int  aux_0 = my_aux_0;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       iss = (iss && (prev < a[i]));
      
      }
    my_iss = iss;
    my_prev = prev;
    my_aux_0 = aux_0;
    
    }
  void  join(ParallelIs_sorted1& x)
    {
     my_iss = ((my_iss && x.my_iss) && ((x.my_aux_0 - my_prev) > (1 - 1)));
    }
};

_Bool  TestIs_sorted1::parallel_apply() const {
  ParallelIs_sorted1 _p_is_sorted_(a);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_is_sorted_);
  return _p_is_sorted_.& is_sorted;
  
}
_Bool  TestIs_sorted1::sequential_apply() const {
  _Bool (int *a , int n ) is_sorted = my_is_sorted;
  int * a = my_a;
  int  n = my_n;
  _Bool  iss = my_iss;
  int  prev = my_prev;
  int  i = my_i;
  int  tmp = my_tmp;
  int  aux_0 = my_aux_0;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
