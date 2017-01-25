#include <iostream>
#include <tbb/tbb.h>
#include "second_max1.h.h"

using namespace tbb;

typedef __iterator_type__ long;

class ParallelSecond_max1 {
private:
  int * my_a;
  
public:
  int  my_m;
  int  my_m2;
  
  ParallelSecond_max1(ParallelSecond_max1& x, split)
    my_a(x.a), my_m(0), my_m2(0) {}
  ParallelSecond_max1(int * a) my_a(a), my_m(0), my_m2(0) {}
  void  operator()()
    {
    int * a = my_a;
    int  m = my_m;
    int  m2 = my_m2;
    
    if (b < 0 || r.begin() < b)
    b = r.begin(); 
    if (e < 0 || r.end() > e)
    e = r.end();
    
    for (__iterator_type__ i = r.begin(); i!= r.end(); ++i) {
       m2 = ((m2 > ((m < a[i]) ? m : a[i])) ? m2 : ((m < a[i]) ? m : a[i]));
       m = ((m > a[i]) ? m : a[i]);
      
      }
    my_m = m;
    my_m2 = m2;
    
    }
};

int  TestSecond_max1::parallel_apply() const {
  ParallelSecond_max1 _p_second_max_(a);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_second_max_);
  return _p_second_max_.m2;
  
}
int  TestSecond_max1::sequential_apply() const {
  int * a = my_a;
  int  n = my_n;
  int  m = my_m;
  int  m2 = my_m2;
  int  i = my_i;
  int  tmp = my_tmp;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
