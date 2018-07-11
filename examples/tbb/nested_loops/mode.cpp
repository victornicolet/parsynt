#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


struct Mode {
    int *A;
    long m;

    int elt;
    int count;
    int max_cnt;
    int mode;

    Mode(int* _input, long rl) : A(_input), m(rl), elt(0), count(0), max_cnt(0), mode(0){}

    Mode(Mode& s, split) {mode = 0; count = 0; max_cnt = 0; elt = 0; A = s.A; m = s.m; }

    void operator()( const blocked_range<long>& r ) {

        for(long i = r.begin(); i != r.end(); ++i) {

            elt = A[i];
            count = 1;

            for(long j = 0; j < m-1; j++) {
                if(A[j] = elt) {
                    count++;
                }
            }

            if (count > max_cnt) {
                mode = elt;
            }
            max_cnt = max(max_cnt, count);

        }
    }

    void join(Mode& r) {
        count = r.count;
        elt = r.elt;
        max_cnt = max(r.max_cnt, max_cnt);
        mode =  (r.max_cnt > max_cnt) ? mode : r.mode;

    }

};

double do_seq(int *A, long m, long n) {
    StopWatch t;
    t.start();

    int elt = 0;
    int mode = 0;
    int count = 0;
    int max_cnt = 0;

    for(long i = 0; i < n; ++i) {

        elt = A[i];
        count = 1;

        for(long j = 0; j < m-1; j++) {
            if(A[j] == elt) {
                count++;
            }
        }

        if (count > max_cnt) {
            mode = elt;
        }
        max_cnt = max(max_cnt, count);

    }

    return t.stop();
}

double do_par(int *input, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    Mode mode(input, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), mode);
        elapsed += t.stop();
    }

    return elapsed / NUM_EXP;
}

int main(int argc, char** argv) {
    // Data size:
    long n = 2 << EXPERIMENTS_N;
    long m = 2 << EXPERIMENTS_M;
    // Data allocation and initialization
    int *input;
    input = (int*) malloc(sizeof(int) * n);
    for(long i = 0; i < n; i++) {
        input[i] = rand() % 10;
    }

    if(argc <= 1) {
        cout << "Usage: Gradient1 [NUMBER OF CORES]" << endl;
        return  -1;
    }

    int num_cores = atoi(argv[1]);
    double exp_time = 0.0;

    if (num_cores > 0) {
        // Do the parallel experiment.
        exp_time = do_par(input, n, n, num_cores);
    } else {
        // Do the sequential experiment.
        exp_time = do_seq(input, n, n);
    }

    cout <<argv[0] << "," << num_cores << "," << exp_time << endl;

    return 0;
}