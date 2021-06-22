#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;

//int col_maxmin(int **A, int m, int n) {
//
//    int *amin;
//    int amaxmin = 0;
//
//    amin = malloc(m * sizeof(amin));
//
//    for(int i = 0; i < n; i++) {
//        amaxmin = 0;
//
//        for(int j = 0; j < n; j++) {
//            amin[j] = min (amin[j], A[i][j]);
//            amaxmin = max(amaxmin, amin);
//        }
//    }
//    return amaxmin;
//}
//
//
///*
//  Join:
//  for j = 1 .. m:
//        amin[j] = min(l.amin[j], r.amin[j]);
//		amaxmin = max(amin[j], amaxmin)
//*/


struct MinMaxCol {
    int **A;
    int *amin;
    int amaxmin;
    long m;

    MinMaxCol(int** _input, long rl) : A(_input), m(rl), amaxmin(INT_MIN){
        amin = new int[rl];
    }

    MinMaxCol(MinMaxCol& s, split) {
        amaxmin = INT_MIN;
        A = s.A;
        m = s.m;
        amin = new int[s.m];
    }

    void operator()( const blocked_range<long>& r ) {
        int _amaxmin = amaxmin;
        int* _amin = amin;

        for(long i = r.begin(); i != r.end(); ++i) {
            for(long j = 0; j < m; j++) {
                _amin[j] = min(_amin[j], A[i][j]);
                _amaxmin = max(_amaxmin, _amin[j]);
            }
        }

        amaxmin = _amaxmin;
        amin = _amin;

    }

    void join(MinMaxCol& rhs) {
        for(long j = 0; j < m; j++) {
            amin[j] = min(amin[j], rhs.amin[j]);
            amaxmin = max(amin[j], amaxmin);
        }
    }

};

double do_seq(int **A, long m, long n) {
    StopWatch t;
    t.start();

    int _amaxmin = INT_MIN;
    int* _amin = new int[m];

    for(long i = 0; i < n; ++i) {
        for(long j = 0; j < m; j++) {
            _amin[j] = min(_amin[j], A[i][j]);
            _amaxmin = max(_amaxmin, _amin[j]);
        }
    }

    return t.stop();
}

double do_par(int **input, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    MinMaxCol minMaxCol(input, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), minMaxCol);
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
            input[i][j] = rand() % 40;
        }
    }

    if(argc <= 1) {
        cout << "Usage: Gradient1 [NUMBER OF CORES]" << endl;
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

    cout <<argv[0] << "," << num_cores << "," << exp_time << endl;

    return 0;
}