#include <iostream>
#include <sstream>
#include <cmath>
#include <tbb/tbb.h>
#include "Examples/Stopwatch.h"

using namespace tbb;


class SumFoo {
    float* my_a;
public:
    double my_sum;
    int my_c;

    void operator()( const blocked_range<size_t>& r )
    {


        float *a = my_a;
        float sum = my_sum;
        size_t end = r.end();


        size_t begin = r.begin();
        int c = my_c;
        for (size_t i = r.end(); i >= begin; i--) {
    	  sum = sum + a[i] / c;
	  c = c << 1;
	}


        my_sum = sum;
        my_c = c;
    }

    SumFoo( SumFoo& x, split ) : my_a(x.my_a), my_sum(0), my_c(1) {}

    void join(const SumFoo& y)
    {
      my_sum = my_sum / y.my_c + y.my_sum;
    }

    SumFoo(float a[]) :
        my_a(a), my_sum(0), my_c(1)
    {}
};

double ParallelSumFoo(float a[], size_t n)
{
    SumFoo sf(a);
    parallel_reduce( blocked_range<size_t>(0,n,10000), sf );
    return sf.my_sum;
}


double SerialSumFoo(float a[], size_t n)
{
    double sum = 0.0;
    for (int i = 0; i < n; i++)
	  sum = (sum + a[i]) / 2.0;
    return sum;
}

double SerialSum(float a[], size_t n)
{
    double sum = 0.0;
    int c = 2;
    for (int i = n-1; i >= 0; i--) {
	  sum = (sum + a[i]) / c;
	  c = c << 1;
	}
    return sum;
}



int main(int argc, const char *argv[])
{
    //tbb::task_scheduler_init init(2);
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

    //StopWatch u;
    //u.start();
    //double sum = ParallelSumFoo(f_array, size);
    //std::cout << "parallel sum: " << sum << " in time: " << u.stop() << "\n";

    StopWatch w;
    w.start();
    double ssum = SerialSumFoo(f_array, size);

    std::cout << "serial sum: " << ssum << " in time: " << w.stop() << "\n";

    //StopWatch v;
    //v.start();
    //double ssum = SerialSum(f_array, size);

    //std::cout << "Other serial sum: " << ssum << " in time: " << v.stop() << "\n";


    delete f_array;
}
