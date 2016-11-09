//
// Created by nicolet on 09/11/16.
//
#include <iostream>
#include <sstream>
#include <cmath>
#include <tbb/tbb.h>
#include "Stopwatch.h"
#include "ExampleUnit.h"

using namespace tbb;

class SumFoo {
    int* my_a;
public:
    int my_sum;
    int b, e;

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
            sum = sum >> 1;
        }

        my_sum = sum;
    }

    SumFoo( SumFoo& x, split ) : my_a(x.my_a), my_sum(0), b(-1), e(-1) {}

    void join(const SumFoo& y)
    {
        int tmp = my_sum;
        for (int i = y.b; i < y.e; i++)
            tmp = tmp >> 1;

        my_sum = tmp + y.my_sum;
        e = y.e;
    }

    SumFoo(int a[]) :
            my_a(a), my_sum(0), b(-1), e(-1)
    {}
};

double ParallelSumFoo(int a[], size_t n)
{
    SumFoo sf(a);
    parallel_reduce(blocked_range<size_t>(0,n,50000), sf );
    return sf.my_sum;
}


double SerialSumFoo(int a[], size_t n)
{
    int sum = 0;
    for (int i = 0; i < n; i++)
        sum += a[i];
    sum = sum >> 1;
    return sum;
}
