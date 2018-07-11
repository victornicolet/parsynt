#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


struct MaxDist {
    int *A;
    int *B;
    int md;
    long m;

    MaxDist(int* _input1, int* _input2, long rl) : A(_input1), B(_input2), m(rl), md(INT_MIN){}

    MaxDist(MaxDist& s, split) {md= INT_MIN; A = s.A;  B = s.B; m = s.m; }

    void operator()( const blocked_range<long>& r ) {
        int _md = md;

        for(long i = r.begin(); i != r.end(); ++i) {
            for(long j = 0; j < m-1; j++) {
                if (A[i] - B[j] > 0) {
                    _md = max(_md, A[i] - B[j]);
                } else {
                    _md = max(_md, B[j] - A[i]);
                }

            }
        }

        md = _md;
    }

    void join(MaxDist& rhs) { md = md + rhs.md; }

};

double do_seq(int *A, int *B, long m, long n) {
    StopWatch t;
    t.start();
    int sum= 0;

    int md = INT_MIN;

    for(long i = 0; i < n; ++i) {
        for(long j = 0; j < m-1; j++) {
            if (A[i] - B[j] > 0) {
                md = max(md, A[i] - B[j]);
            } else {
                md = max(md, B[j] - A[i]);
            }

        }
    }

    return t.stop();
}

double do_par(int *a, int *b, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    MaxDist sum(a, b, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), sum);
        elapsed += t.stop();
    }

    return elapsed / NUM_EXP;
}

int main(int argc, char** argv) {
    // Data size:
    long n = 2 << EXPERIMENTS_N;
    long m = 2 << EXPERIMENTS_M;
    // Data allocation and initialization
    int *input1;
    int * input2;
    input1 = new int[n];
    input2 = new int[m];
    for(long i = 0; i < n; i++) {
        input1[i] = rand() % 255 - 12;
    }
    for(long j =0; j < m; j++){
        input2[j] = rand() % 40;
    }


    if(argc <= 1) {
        cout << "Usage: Gradient1 [NUMBER OF CORES]" << endl;
        return  -1;
    }

    int num_cores = atoi(argv[1]);
    double exp_time = 0.0;

    if (num_cores > 0) {
        // Do the parallel experiment.
        exp_time = do_par(input1, input2, m, n, num_cores);
    } else {
        // Do the sequential experiment.
        exp_time = do_seq(input1, input2, m, n);
    }

    cout <<argv[0] << "," << num_cores << "," << exp_time << endl;

    return 0;
}