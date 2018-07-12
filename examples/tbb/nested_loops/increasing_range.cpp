#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;
//
//int high = 0;
//int phigh = 0;
///*
//  int in_aux = MAX_INT
//*/
//for(int i = 0; i < n; i++) {
//high = MIN_INT;
//for(int j = 0; j < m; j++) {
//
//if (A[i][j] <= phigh) {
//incr = 0;
//}
//
///* in_aux = min(in_aux, A[i][j]); */
//high = max(high, A[i][j]);
//}
//phigh = high;
//}
//
//return incr;
//}



struct Increases {
    int **A;
    long m;

    int high;
    int phigh;
    int aux;
    bool incr;

    Increases(int** _input, long rl) : A(_input), m(rl),
                                       high(0), phigh(0), aux(INT_MIN), incr(true) {}

    Increases(Increases& s, split) {
        high = 0; phigh = 0; aux = INT_MIN;
        A = s.A;
        m = s.m;
        incr = true;
    }

    void operator()( const blocked_range<long>& r ) {

        long e = r.begin();

        for(long i = e; i != r.end(); ++i)
        {
            high = INT_MIN;
            for(int j = 0; j < m; j++) {

                if (A[i][j] <= phigh) {
                    incr = 0;
                }

                aux = min(aux, A[i][j]);
                high = max(high, A[i][j]);
            }
            phigh = high;
        }
    }

    void join(Increases& r) {
        aux = min(aux, r.aux);
        high = r.high;
        phigh = r.phigh;
        incr = incr && (r.aux <= phigh) ? false : r.incr;
    }

};

double do_seq(int **A, long m, long n) {
    StopWatch t;
    t.start();
    int sum= 0;

    int low, high;
    int l = 0;
    int h = 0;
    bool incl = true;


    for(long i = 0; i < n; ++i) {
        low = 0;
        high = 0;

        for(long j = 0; j < m; j++) {
            high = max(high, A[i][j]);
            low = min(low, A[i][j]);
        }

        h = min(h, high);
        l = min(l, low);

        incl = incl && h > l;

    }

    return t.stop();
}

double do_par(int **input, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    Increases pv(input, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), pv);
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