#include <iostream>
#include <tbb/tbb.h>
#include "linear_search_pos2.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelLinear_search_pos2 {
private:
  int * my_a;
  int  my_x;
  
public:
  int  my_pos;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  
  
  ParallelLinear_search_pos2(ParallelLinear_search_pos2& x, split):
    my_a(x.a), my_x(x.x), my_pos(-1), my_i_begin_(-1), my_i_end_(-1) {
    }
  
  ParallelLinear_search_pos2(int * a, int  x):
    my_a(a), my_x(x), my_pos(-1), my_i_begin_(-1), my_i_end_(-1) {}
  
  
  void  operator()(const blocked_range<__iterator_type__>& _r_)
    {
    int * a = my_a;
    int  x = my_x;
    int  pos = my_pos;
    int  i = my_i;
    
    if (my_i_begin_ < 0 || _r_.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || _r_.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = _r_.begin(); i!= _r_.end(); ++i) {
       pos = ((a[i] = x) ? i : pos);
      
      }
    my_pos = pos;
    
    }
  void  join(ParallelLinear_search_pos2& x)
    {
     my_pos = ((x.my_pos >= (x.my_pos - x.my_pos)) ? x.my_pos : my_pos);
    }
};

int  TestLinear_search_pos2::parallel_apply() const {
  ParallelLinear_search_pos2 _p_linear_search_pos_(a, x);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_linear_search_pos_);
  return _p_linear_search_pos_.pos;
  
}
int  TestLinear_search_pos2::sequential_apply() const {
  int  n = my_n;
  int * a = my_a;
  int  x = my_x;
  int  pos = my_pos;
  int  i = my_i;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
