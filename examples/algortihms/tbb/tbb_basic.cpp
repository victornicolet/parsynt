// For a simple debug build use icc example.cpp -ltbb_debug
#include "tbb/tbb.h"
#include <iostream>
#include <cfloat>
using namespace tbb;

/*
  Examples from the Intel TBB tutorials and Getting Started Guides
  1 - Parallel For examples 
  2 - Parallel reduction examples
  3 - Custom iteration spaces
 */

/*
******************************************
1 - Parallel For examples
*/
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

// Partionning using chunksize
// Using a simple partitioner will ensure  G/2 <= chunksize <= G
const size_t G = 128;
void ParallelApplyG (float * a, size_t n) {
  parallel_for(blocked_range<size_t>(0, n, G), ApplyFoo(a),
			   simple_partitioner());
}

// Affinity partionner is good at improving cache locality
// For example in a time-dependent loop
void ParallelApplyFooAffinity (float * a, size_t n) {
  static affinity_partitioner ap;
  parallel_for(blocked_range<size_t>(0,n), ApplyFoo(a), ap);
}

void TimeStepFoo (float * a, size_t n, int steps) {
  for(int i = 0; i < steps; i++) {
	ParallelApplyFooAffinity(a, n);
  }
}

/* 
******************************************
2 - Parallel reductions examples
*/
class SumBase {
  float * my_a;
public:
  float my_sum;
  void operator() (const blocked_range<size_t>& r) {
	float *a = my_a;
	float sum = my_sum;
	for(size_t i = r.begin(); i != r.end(); i++)
	  sum += a[i];
	my_sum = sum;
  }
  
  /*
	Split constructor : takes a second argument of type split
	provided by the library. This is the constructor used by a
	thread that "steals" work from another thread, copying the 
	object and then doing the work.
  */ 
  SumBase(SumBase& x, split): my_a(x.my_a), my_sum(0) {}
  
  /* 
	 The join method is then called to join the work done
	 by another thread in its "copy" of the object. In this
	 case we have a simple operation : adding the sum computed
  */
  void join(const SumBase& y) { my_sum += y.my_sum; }

  // Default constructor
  SumBase(float a[]):
	my_a(a), my_sum(0) {}
};

/*
  The use of parallel_reduce here is quite similar to the use of
  the previous construct, parallel_for. We return the result, 
  stored in the object we pass to the parallel reduce 
*/
float ParallelSumFoo (float * a, size_t n) {
  SumBase sf(a);
  parallel_reduce(blocked_range<size_t>(0, n), sf);
  return sf.my_sum;
}

/*
  Now a more advanced example of reduction where some information
  has to be kept between the threads.
*/
class MinIndex {
  float * my_a;
public:
  float min_val;
  size_t min_index;

  void operator() (const blocked_range<size_t>& r) {
	float loc_min_val = min_val;
	size_t loc_min_index = min_index;
	for(size_t i = r.begin(); i != r.end(); i++) {
	  if(my_a[i] < loc_min_val) {
		loc_min_index = i;
		loc_min_val = my_a[i];
	  }
	}
	min_val = loc_min_val;
	min_index = loc_min_index;
  }

  MinIndex(MinIndex &x, split):
	min_val(FLT_MAX),
	min_index(-1),
	my_a(x.my_a)
  {}
  
  void join(const MinIndex &y) {
	if(y.min_val < min_val) {
	  min_val = y.min_val;
	  min_index = y.min_index;
	}
  }

  MinIndex(float a[]):
	min_val(FLT_MAX),
	min_index(-1),
	my_a(a)
  {}
};

// Find the minimum of the array a in a loop.
size_t ParalleMinIndex(float *a, size_t n) {
  MinIndex mi(a);
  parallel_reduce(blocked_range<size_t>(0, n), mi);
  return mi.min_val;
}

/*
*********************************************
3 - Other kind of iteration spaces
 */

/* 
   Using TBB we can specify other kind of iteration spaces.
   WIP: show a more complex iteration space
*/

class Sis {
public:
  size_t my_top;
  size_t my_bot;
  // True if range is empty
  bool empty() const;
  // True if range can be split into non-empty subranges
  bool is_divisible() const;
  // Splits r into subranges r and *this
  Sis( Sis& r, split );
  // Splits r into subranges r and *this in proportion p
  Sis( Sis& r, proportional_split p );
  // Allows usage of proportional splitting constructor
  static const bool is_splittable_in_proportion = false;
};

bool Sis::empty() const {
  return my_top == my_bot;
}

bool Sis::is_divisible() const {
  return (my_top - my_bot) > 32;
}

Sis::Sis(Sis& r, split) {
  size_t middle = (my_top - my_bot) / 2;
  r.my_bot = middle + 1;
  r.my_top = my_top;
  my_top = middle;
}

Sis::Sis(Sis& r, proportional_split p) {
  size_t middle = (my_top - my_bot) / 2;
  r.my_bot = middle + 1;
  r.my_top = my_top;
  my_top = middle;
}

int main (int argc, char* argv[]) {
  float a[] = { 0.23, 0.2 , 0 , 0, 0.36, 0.25};
  ParallelApplyFoo(a, 6);
  return 0;
}


