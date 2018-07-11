#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


struct MinMax {
    int **A;
    int amin;
    int amax;
    long m;

    MinMax(int** _input, long rl) : A(_input), m(rl), amin(INT_MAX), amax(INT_MIN){}

    MinMax(MinMax& s, split) {
        amax = INT_MIN;
        amin = INT_MAX;
        A = s.A;
        m = s.m;
    }

    void operator()( const blocked_range<long>& r ) {
        int _amax = amax;
        int _amin = amin;
        for(long i = r.begin(); i != r.end(); ++i) {
            _amin = INT_MAX;
            for(long j = 0; j < m-1; j++) {
                _amin = min(_amin, A[i][j]);
            }
            _amax = max(_amax, _amin);
        }
        amax = _amax;
        amin = _amin;
    }

    void join(MinMax& rhs) {
        amax = max(amax, rhs.amax);
        amin = rhs.amin;
    }
};

double do_seq(int **A, long m, long n) {
    StopWatch t;
    t.start();
    int amax = INT_MIN;
    int amin = INT_MAX;

    for(long i = 0; i < n - 1; ++i) {
        amin = INT_MAX;
        for(long j = 0; j < m-1; j++) {
            amin = min (amin, A[i][j]);
        }
        amax = max(amax, amin);
    }

    return t.stop();
}

double do_par(int **input, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    MinMax minMax(input, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n), minMax);
        elapsed += t.stop();
    }

    return elapsed / NUM_EXP;
}

int main(int argc, char** argv) {
    // Data size:
    long n = 2 << EXPERIMENTS_N;
    long m = 2 << EXPERIMENTS_M;
    // Data allocation and initialization
    int **input;
    input = (int**) malloc(sizeof(int*) * n);
    for(long i = 0; i < n; i++) {
        input[i] = (int*) malloc(sizeof(int) * m);
        for(long j =0; j < m; j++){
            input[i][j] = (rand() % 255) - 125;
        }
    }

    if(argc <= 1) {
        cout << "Usage: MinMax [NUMBER OF CORES]" << endl;
        return  -1;
    }

    int num_cores = atoi(argv[1]);
    double exp_time = 0.0;

    if (num_cores > 0) {
        // Do the parallel experiment.
        exp_time = do_par(input, m, n, num_cores);
    } else {
        // Do the sequential experiment.
        exp_time = do_seq(input, m, n);
    }

    cout << argv[0] << "," << num_cores << "," << exp_time << endl;

    return 0;
}