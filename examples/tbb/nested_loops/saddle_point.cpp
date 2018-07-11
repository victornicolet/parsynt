#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


struct SaddlePoint {
    int **A;
    long m;
    int* colm;
    int mcols = 0;
    int xrows = 0;
    int rowx = 0;


    SaddlePoint(int** _input, long rl) : A(_input), m(rl), mcols(INT_MIN), xrows(INT_MIN), rowx(INT_MIN) {
        colm = new int[rl];
        for(long j = 0; j < rl; j ++) {
            colm[j] = INT_MAX;
        }
    }

    SaddlePoint(SaddlePoint& s, split) {
        A = s.A;
        m = s.m;
        mcols = INT_MIN;
        xrows = INT_MIN;
        rowx = INT_MIN;
        colm = new int[s.m];
        for(long j = 0; j < s.m; j ++) {
            colm[j] = INT_MAX;
        }
    }

    void operator()( const blocked_range<long>& r ) {

        for(long i = r.begin(); i != r.end(); i++)
        {
            rowx = INT_MIN;
            for(long j = 0; j < m; j++)
            {
                rowx = max(rowx, A[i][j]);
                colm[j] = min(colm[j], A[i][j]);
                mcols = max(colm[j], mcols);
            }
            xrows = min(rowx, xrows);
        }
    }

    void join(SaddlePoint& r) {
        for(long j = 0; j < m; j++) {
            colm[j] = min(colm[j], r.colm[j]);
            mcols = max(colm[j], mcols);
        }
        rowx = r.rowx;
        xrows = min(xrows, r.xrows);


    }
};

double do_seq(int **A, long m, long n) {
    StopWatch t;
    t.start();

    int rowx = INT_MIN;
    int mcols = INT_MIN;
    int xrows = INT_MIN;
    int* colm;
    colm = new int[m];
    for(long j = 0; j < m; j ++) {
        colm[j] = INT_MAX;
    }

    for(long i = 0; i < n; ++i) {
        rowx = INT_MIN;
        for(long j = 0; j < m; j++) {
            rowx = max(rowx, A[i][j]);
            colm[j] = min(colm[j], A[i][j]);
            mcols = max(colm[j], mcols);
        }
        xrows = min(rowx, xrows);
    }

    return t.stop();
}

double do_par(int **input, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    SaddlePoint sd(input, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n), sd);
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