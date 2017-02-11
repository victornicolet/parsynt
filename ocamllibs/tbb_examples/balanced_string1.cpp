#include <iostream>
#include <tbb/tbb.h>
#include "balanced_string1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelBalanced_string1 {
private:
  _Bool * my_a;
  
public:
  _Bool  my_bal;
  int  my_cnt;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  int  my_aux_3;
  
  
  ParallelBalanced_string1(ParallelBalanced_string1& x, split):
    my_a(x.a), my_bal(#t), my_cnt(0), my_i_begin_(-1), my_i_end_(-1), my_aux_3(0) {
    }
  
  ParallelBalanced_string1(_Bool * a):
    my_a(a), my_bal(#t), my_cnt(0), my_i_begin_(-1), my_i_end_(-1), my_aux_3(0) {
    }
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    _Bool * a = my_a;
    _Bool  bal = my_bal;
    int  cnt = my_cnt;
    int  aux_3 = my_aux_3;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       cnt = (cnt + (a[i] ? 1 : -1));
       bal = (bal && ((cnt + (a[i] ? 1 : -1)) >= 0));
       aux_3 = ((cnt < aux_3) ? cnt : aux_3);
      
      }
    my_bal = bal;
    my_cnt = cnt;
    my_aux_3 = aux_3;
    
    }
  void  join(ParallelBalanced_string1& x)
    {
     my_cnt = (my_cnt + (() ? x.my_cnt : x.my_cnt));
     my_bal = (my_bal && (((my_cnt - 3) + (() ? -1 : (x.my_cnt - x.my_cnt))) >= 
                           (-3 - x.my_aux_3)));
     my_aux_3 = (((x.my_aux_3 + my_cnt) < my_aux_3) ? (x.my_aux_3 + my_cnt) :
                  my_aux_3);
    }
};

_Bool  TestBalanced_string1::parallel_apply() const {
  ParallelBalanced_string1 _p_balanced_string_(a);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_balanced_string_);
  return _p_balanced_string_.bal;
  
}
_Bool  TestBalanced_string1::sequential_apply() const {
  _Bool * a = my_a;
  int  n = my_n;
  _Bool  bal = my_bal;
  int  cnt = my_cnt;
  int  i = my_i;
  int  tmp = my_tmp;
  int  tmp___0 = my_tmp___0;
  int  aux_3 = my_aux_3;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
