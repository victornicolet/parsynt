#include <iostream>
#include <sstream>
#include <cmath>
#include <tbb/tbb.h>
#include "Stopwatch.h"

using namespace tbb;
 

class SumFoo {
    float* my_a;
public:
    double my_sum; 
    int b, e;

    void operator()( const blocked_range<size_t>& r ) 
    {


        float *a = my_a;
        float sum = my_sum;
        size_t end = r.end();

	if (b < 0 || r.begin() < b)
	    b = r.begin();
	if (e < 0 || r.end() > e)
	    e = r.end();

        for (size_t i=r.begin(); i!=end; ++i) {
            sum = (sum + a[i]) / 2.0; 
        }
            
        my_sum = sum;    
    }
 
    SumFoo( SumFoo& x, split ) : my_a(x.my_a), my_sum(0), b(-1), e(-1) {}
 
    void join(const SumFoo& y) 
    { 

	double tmp = my_sum;
	for (int i = y.b; i < y.e; i++)
	    tmp = tmp / 2.0;

	my_sum = tmp + y.my_sum;
	e = y.e;
    }
             
    SumFoo(float a[]) :
        my_a(a), my_sum(0), b(-1), e(-1)
    {}
};

double ParallelSumFoo(float a[], size_t n) 
{
    SumFoo sf(a);
    parallel_reduce( blocked_range<size_t>(0,n,50000), sf );
    return sf.my_sum;
}


double SerialSumFoo(float a[], size_t n) 
{
    double sum = 0.0;
    for (int i = 0; i < n; i++)
	sum = (sum + a[i]) / 2.0;
    return sum;
}

int main(int argc, const char *argv[])
{
    tbb::task_scheduler_init init(4);
    if (argc < 2)
    {
	std::cout << "no array size specified\n";
	exit(1);
    }

    int size = std::atoi(argv[1]);

    std::cout << "array size: " << size << "\n"; 

    float *f_array = new float[size];

    for (int i = 0; i < size; i++)
	f_array[i] = i;
    
    std::cout << "Initialization over.\n";

    StopWatch u; 
    u.start();
    double sum = ParallelSumFoo(f_array, size);
    std::cout << "parallel sum: " << sum << " in time: " << u.stop() << "\n";

    StopWatch w; 
    w.start();
    double ssum = SerialSumFoo(f_array, size);
     
    std::cout << "serial sum: " << ssum << " in time: " << w.stop() << "\n";

    delete f_array;
}
