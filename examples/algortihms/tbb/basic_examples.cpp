#include "tbb/tbb.h"
#include <iostream>
#include <map>
#include <cassert>

using namespace std;
using namespace tbb;

class ApplyPrefixSum {
  int * m_array;
  size_t lb, rb;
public:
  void operator() (const blocked_range<size_t> &r) {
    int leftval = m_array[r.begin() - 1];
    for(size_t i = r.begin(); i != r.end(); i++) {
      m_array[i] = leftval + m_array[i];
      leftval = m_array[i];
    }
    rb = r.end();
  }

  ApplyPrefixSum(ApplyPrefixSum &x, split) {
    m_array = x.m_array;
    lb = x.rb + 1;
    rb = -1;
  }

  void join(const ApplyPrefixSum &x) {
    assert(rb = x.lb - 1);
    cout << "Update " << x.lb << ":" << x.rb << " region by adding " << m_array[rb]
	 << " in " << rb << endl;
    
    for(size_t i = x.lb; i < x.rb; i++) {
      m_array[i] = x.m_array[i] + m_array[rb];
    }
    rb = max(rb, x.rb);
  }

  ApplyPrefixSum(int *a): m_array(a), lb(0), rb(0)
  {}

  int get_elt(size_t index) {
    return m_array[index];
  }
};

  

int main(int argc, char **argv) {
  size_t sz = 10000;
  int* array = new int[sz];
  for(size_t i = 0; i < sz; i++){
    array[i] = 1;
  }
  array[0] = 1;
  ApplyPrefixSum x(array);
  parallel_reduce(blocked_range<size_t>(1,sz), x);
  delete[] array;
  return 0;
}
