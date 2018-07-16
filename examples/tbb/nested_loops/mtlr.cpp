#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


//int *c;
//int mtr = 0;
//int mtrl = 0;
//int sum;
///*
//   int * aux;
// */
//
//for (int i = 0; i < n; i++) {
//sum = 0;
//mtr = 0;
//for(int j = 0; j < m; j++){
//sum += a[i][j];
//c[j] += sum;
//mtr = max(c[j], mtr);
///* Auxiliary:
//   aux[j] = max(aux[j], c[j]);
//*/
//}
//mtrl = max(mtr, mtrl);
//}
//return mtrl;

struct MTLR {
    int **A;
    long m;

    int *c;
    int *aux;
    int mtr;
    int mtlr;
    int sum;


    MTLR(int** _input, long rl) : A(_input), m(rl), sum(0), mtr(0), mtlr(0){
        c = new int[rl];
        aux = new int[rl];
    }

    MTLR(MTLR& s, split) {
        sum = 0;
        mtr = 0;
        mtlr = 0;
        c = new int[s.m];
        aux = new int[s.m];
        A = s.A;
        m = s.m;

    }

    void operator()( const blocked_range<long>& r ) {

        for (long i = r.begin(); i != r.end(); i++) {
            sum = 0;
            mtr = 0;
            for (long j = 0; j < m; j++) {
                sum += A[i][j];
                c[j] += sum;
                mtr = max(c[j], mtr);
                aux[j] = max(aux[j], c[j]);
            }
            mtlr = max(mtr, mtlr);
        }
    }

    void join(MTLR& r) {
        mtr = 0;
        for(long j = 0; j < m; j++){
            c[j] = c[j] + r.c[j];
            aux[j] = max(aux[j], c[j] + r.aux[j]);
            mtr = max(mtr, aux[j]);
        }
        mtlr = max(mtr, mtlr);
    }

};

double do_seq(int **A, long m, long n) {
    StopWatch t;
    t.start();
    int sum= 0;

    for(long i = 0; i < n - 1; ++i) {
        for(long j = 0; j < m-1; j++) {
            sum += A[i][j];
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

    MTLR sum(input, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n), sum);
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