#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


struct MaxLeftRec {
    int **A;
    long m;
    int rs;
    int mlr;
    int *rects;

    MaxLeftRec(int** _input, int* rects, long rl) : A(_input), m(rl), rs(0), mlr(0), rects(rects) {}

    MaxLeftRec(MaxLeftRec& s, split) {mlr = 0; rs = 0; A = s.A; m = s.m; rects = s.rects; }

    void operator()( const blocked_range<long>& r ) {
        int lrs = 0;
        int lmlr = 0;

        for(long i = r.begin(); i != r.end(); ++i) {
            lrs = 0;
            lmlr = 0;
            for(long j = 0; j < m; j++) {
                lrs += A[i][j];
                rects[j] += lrs;
                lmlr = max(lmlr, rects[j]);
            }
        }
        lmlr = mlr;
        lrs = rs;
    }

    void join(MaxLeftRec& rhs) {
        mlr = 0;
        rs = rhs.rs;
        for(long j = 0; j < m; j++) {
            rects [j] += rhs.rects[j];
            mlr = max(mlr, rects[j]);
        }
    }

};

double do_seq(int **A, long m, long n) {

    int* rects = (int*) calloc(m, sizeof(int));

    StopWatch t;
    t.start();
    bool b;
    int rs = 0;
    int mlr = 0;

    for(long i = 0; i < n; ++i) {
        rs = 0;
        mlr = 0;
        for(long j = 0; j < m; j++) {
            rs += A[i][j];
            rects[j] += rs;
            mlr = max(mlr, rects[j]);
        }
    }

    return t.stop();
}

double do_par(int **input, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // Any specific initalization of state variables must be done here.
    int * rects = (int*) calloc(m, sizeof(int));
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    MaxLeftRec mlr(input, rects,  m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), mlr);
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
            input[i][j] = static_cast<int>(i + j);
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