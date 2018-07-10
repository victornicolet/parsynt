#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


struct MaxTopStrip {
    int **A;
    long m;
    int tss;
    int mts;
    int *rects;

    MaxTopStrip(int** _input, int* rects, long rl) : A(_input), m(rl), tss(0), mts(0), rects(rects) {}

    MaxTopStrip(MaxTopStrip& s, split) {mts = 0; tss = 0; A = s.A; m = s.m; rects = s.rects; }

    void operator()( const blocked_range<long>& r ) {
      for(int i = r.begin(); i < r.end(); i++)
        {
          for(int j = 0; j < m; j++)
            {
              tss += A[i][j];
            }
          mts = max(mts, tss);
        }

    }
    
    // To do
    void join(MaxTopStrip& rhs) {
        int aux = tss;
        tss = rhs.tss+tss;
        mts = max(mts,rhs.mts+aux);
        for(long j = 0; j < m; j++) {
            rects [j] += rhs.rects[j];
            mts = max(mts, rects[j]);
        }
    }

};

double do_seq(int **A, long m, long n) {

    int* rects = (int*) calloc(m, sizeof(int));

    StopWatch t;
    t.start();
    int top_strip_sum = 0;
    int max_top_strip = 0;
    int strip_sum = 0;
    for(int i = 0; i < n; i++)
    {
      for(int j = 0; j < m; j++)
        {
          top_strip_sum += A[i][j];
        }
      max_top_strip = max(max_top_strip, top_strip_sum);
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

    MaxTopStrip mlr(input, rects, m);

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
