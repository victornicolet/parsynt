#include <iostream>
#include <tbb/tbb.h>
#include "compute_least_squares1.h"

using namespace tbb;

typedef long  __iterator_type__;

class ParallelCompute_least_squares1 {
private:
  int * my_x;
  int * my_y;
  
public:
  int  my_SUMx;
  int  my_SUMy;
  int  my_SUMxy;
  int  my_SUMxx;
  __iterator_type__  my_i_begin_;
  __iterator_type__  my_i_end_;
  
  
  ParallelCompute_least_squares1(ParallelCompute_least_squares1& x, split):
    my_x(x.x), my_y(x.y), my_SUMx(0), my_SUMy(0), my_SUMxy(0), my_SUMxx(0), my_i_begin_(-1), my_i_end_(-1) {
    }
  
  ParallelCompute_least_squares1(int * x, int * y):
    my_x(x), my_y(y), my_SUMx(0), my_SUMy(0), my_SUMxy(0), my_SUMxx(0), my_i_begin_(-1), my_i_end_(-1) {
    }
  
  
  void  operator()(const blocked_range<__iterator_type__>& r)
    {
    int * x = my_x;
    int * y = my_y;
    int  SUMx = my_SUMx;
    int  SUMy = my_SUMy;
    int  SUMxy = my_SUMxy;
    int  SUMxx = my_SUMxx;
    
    if (my_i_begin_ < 0 || r.begin() < my_i_begin_)
    my_i_begin_ = r.begin(); 
    if (my_i_end_ < 0 || r.end() > my_i_end_)
    my_i_end_ = r.end();
    
    for (__iterator_type__ i = r.begin(); i!= r.end(); ++i) {
       SUMxx = (SUMxx + (x[i] * x[i]));
       SUMxy = (SUMxy + (x[i] * y[i]));
       SUMy = (SUMy + y[i]);  SUMx = (SUMx + x[i]);
      
      }
    my_SUMx = SUMx;
    my_SUMy = SUMy;
    my_SUMxy = SUMxy;
    my_SUMxx = SUMxx;
    
    }
  void  join(const blocked_range<__iterator_type__>& r)
    {
     my_SUMxx = (my_SUMxx + x.my_SUMxx);
     my_SUMxy = (((my_SUMxy + 1) - 1) + x.my_SUMxy);
     my_SUMy = (x.my_SUMy + my_SUMy);
     my_SUMx = ((x.my_SUMx + 1) + (my_SUMx - 1));
    }
};

int  TestCompute_least_squares1::parallel_apply() const {
  ParallelCompute_least_squares1 _p_compute_least_squares_(x, y);
  parallel_reduce(blocked_range<__iterator_type__>(0,n,1000000), _p_compute_least_squares_);
  return _p_compute_least_squares_.(SUMx * SUMy - n * SUMxy) / (SUMx * SUMx - n * SUMxx);
  
}
int  TestCompute_least_squares1::sequential_apply() const {
  int  n = my_n;
  int * x = my_x;
  int * y = my_y;
  int  SUMx = my_SUMx;
  int  SUMy = my_SUMy;
  int  SUMxy = my_SUMxy;
  int  SUMxx = my_SUMxx;
  int  i = my_i;
  
  \* FILL THE BLOCK HERE *\;
  return sum;
  
}
