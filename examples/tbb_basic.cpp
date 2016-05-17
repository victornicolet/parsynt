// For a simple debug build use icc example.cpp -ltbb_debug
#include "tbb/tbb.h"
#include <iostream>
using namespace tbb;

void Foo(int x) {
  int a = x + x;
}
// Write the loop body as a body object
class ApplyFoo {
  float *const my_a;
public:
  void operator()(const blocked_range<size_t> &r) const {
	float *a = my_a;
	for(size_t i = r.begin(); i != r.end(); ++i)
	  Foo(a[i]);
  }

  // Constructor initializes the body object
  ApplyFoo( float a[]):
	my_a(a)
  {}
};

void ParallelApplyFoo (float a[], size_t n) {
  parallel_for(blocked_range<size_t>(0, n) , ApplyFoo(a));
}

// Using lanbda expressions
// Must add C++11 support : icc -std=c++0x ...
void ParallelApplyFoo2 (float * a, size_t n) {
  parallel_for(blocked_range<size_t>(0,n),
			   [=](const blocked_range<size_t>& r) {
				 for(size_t i = r.begin(); i != r.end(); ++i)
				   Foo(a[i]);
			   }
			   );
}

// Previous example rewritten in much more compact form
void ParallelApplyFoo3 (float * a, size_t n) {
  parallel_for(size_t(0), n, [=](size_t i){Foo(a[i]);});
}

int main (int argc, char* argv[]) {
  float a[] = { 0.23, 0.2 , 0 , 0, 0.36, 0.25};
  ParallelApplyFoo(a, 6);
  return 0;
}


