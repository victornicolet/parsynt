#include <iostream>
#include <tbb/tbb.h>
#include "ExampleUnit.h"
#include "Examples.h"

using namespace tbb;

class SumFoo {
    int* my_a;
public:
    int my_sum;
    int b, e;

    SumFoo(int a[]) : my_a(a), my_sum(0), b(-1), e(-1)  {}
    SumFoo( SumFoo& x, split ) : my_a(x.my_a), my_sum(0), b(-1), e(-1) {}


    void operator()( const blocked_range<size_t>& r )
    {
        int *a = my_a;
        int sum = my_sum;
        size_t end = r.end();

        if (b < 0 || r.begin() < b)
            b = (int) r.begin();
        if (e < 0 || r.end() > e)
            e = (int) r.end();

        for (size_t i = r.begin(); i!=end; ++i) {
            sum +=  a[i];
        }

        my_sum = sum;
    }

    void join(const SumFoo& y) {
        my_sum = my_sum + y.my_sum;
        e = y.e;
    }
};

string ExampleSumFoo::name = "SumFoo";

void ExampleSumFoo::init() {
    if(a == nullptr) {
        cout << "Initialization ..." << endl;
        a = new int[n];
        for (int i = 0; i < n; i++)
            a[i] = i;
        cout << "Initialization terminated." << endl;
    }
}

ExampleSumFoo::~ExampleSumFoo() {
    delete a;
}

double ExampleSumFoo::parallel_apply() const {
    SumFoo sf(a);
    parallel_reduce(blocked_range<size_t>(0,n,1000000), sf );
    return sf.my_sum;
}

double ExampleSumFoo::seq_apply() const {
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += a[i];
    sum = sum >> 1;
    return sum;
}


void ExampleSumFoo::print_result(ostream &out) const {
    StopWatch u;
    u.start();
    double result = parallel_apply();
    double elapsed = u.stop();
    out << "Example " << name << endl;
    out << "Parallel : " <<  result << " in time : " << elapsed << endl;
    StopWatch w;
    w.start();
    double seq_res = seq_apply();
    out << "Serial : " << seq_res << " in time: " << w.stop() << endl;
}

