#include <iostream>
#include <tbb/tbb.h>
#include "second_smallest2.h.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelSecond_smallest2 {
private:
  int * my_a;
  
public:
  int  my_m;
  int  my_m2;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  
  ParallelSecond_smallest2(ParallelSecond_smallest2& x, split):
    my_a(x.a), my_m(0), my_m2(0), my_i_begin_(-1), my_i_end_(-1) {}
  
  ParallelSecond_smallest2(int * a):
    my_a(a), my_m(0), my_m2(0), my_i_begin_(-1), my_i_end_(-1) {}
  
  void  operator()(const blocked_range<__iterator_type__>& r)
    {
    int * a = my_a;
    int  m = my_m;
    int  m2 = my_m2;
    
    if (my_i_begin_ < 0 || r.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || r.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = r.begin(); i!= r.end(); ++i) {
       m2 = ((m2 < ((m > a[i]) ? m : a[i])) ? m2 : ((m > a[i]) ? m : a[i]));
       m = ((m < a[i]) ? m : a[i]);
      
      }
    my_m = m;
    my_m2 = m2;
    
    }
  void  join(const blocked_range<__iterator_type__>& r)
    {
     m2 = ((((x.m > m) ? x.m : m) < ((x.m2 < m2) ? x.m2 : m2)) ?
            ((x.m > m) ? x.m : m) : ((x.m2 < m2) ? x.m2 : m2));
     m = ((((x.m < m) ? x.m : m) < (m + 1)) ? ((x.m < m) ? x.m : m) :
           (m + 1));
    }
};

int  TestSecond_smallest2::parallel_apply() const {
  ParallelSecond_smallest2 _p_second_smallest_(a);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_second_smallest_);
  return _p_second_smallest_.m2;
  
}
int  TestSecond_smallest2::sequential_apply() const {
  int * a = my_a;
  int  n = my_n;
  int  m = my_m;
  int  m2 = my_m2;
  int  i = my_i;
  int  tmp = my_tmp;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
