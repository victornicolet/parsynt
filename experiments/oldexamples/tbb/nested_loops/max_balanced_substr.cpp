#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;
//
//int mwbss(_Bool *a, int m, int n) {
//    int max_length = 0;
//    int offset = 0;
//    _Bool balance = 1;
//
//    for(int i = 0; i < n; i++) {
//        offset = 0;
//        balance = 1;
//
//        for(int j = i; j < n; j++) {
//
//            offset += a[j] ? 1 : -1;
//
//            if (offset == 0 && balance) {
//                max_length = max(max_length, j - i + 1);
//            }
//            if (offset <= 0 ) {
//                balance = 0;
//            }
//        }
//    }
//
//    return max_length;
//}
//
///*
//  Join:
//  offset = r.offset
//  balance = r.balance
//  max_length = max(r.max_length, l.max_length)
//*/


struct MWSS {
    bool *A;
    long m;

    int max_length;
    int offset;
    bool balance;

    MWSS(bool* _input, long rl) : A(_input), m(rl), max_length(0), offset(0), balance(true) {}

    MWSS(MWSS& s, split) {
        max_length = 0;
        offset = 0;
        balance = 0;
        A = s.A;
        m = s.m;
    }

    void operator()( const blocked_range<long>& r ) {

        for(long i = r.begin(); i != r.end(); ++i) {
            offset = 0;
            balance = true;

            for(long j = i; j < m; j++) {

                offset += A[j] ? 1 : -1;

                if (offset == 0 && balance) {
                    max_length = max(max_length, static_cast<int>(j - i + 1));
                }

                if (offset <= 0 ) {
                    balance = false;
                }
            }
        }

    }

    void join(MWSS& r) {
        offset = r.offset;
        balance = r.balance;
        max_length = max(r.max_length, max_length);

    }

};

double do_seq(bool*A, long m, long n) {
    StopWatch t;
    t.start();


    int offset;
    int max_length;
    bool balance;

    for(long i = 0; i < n; ++i) {
        offset = 0;
        balance = true;

        for(long j = i; j < m; j++) {

            offset += A[j] ? 1 : -1;

            if (offset == 0 && balance) {
                max_length = max(max_length, static_cast<int>(j - i + 1));
            }

            if (offset <= 0 ) {
                balance = false;
            }
        }
    }


    return t.stop();
}

double do_par(bool *input, long m, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    MWSS sum(input, m);

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
    bool* input;
    input = new bool[m];

    for(long j =0; j < m; j++){
        input[j] = (rand() % 40) > 0;
    }


    if(argc <= 1) {
        cout << "Usage: Gradient1 [NUMBER OF CORES]" << endl;
        return  -1;
    }

    int num_cores = atoi(argv[1]);
    double exp_time = 0.0;

    if (num_cores > 0) {
        // Do the parallel experiment.
        exp_time = do_par(input, m, m, num_cores);
    } else {
        // Do the sequential experiment.
        exp_time = do_seq(input, m, m);
    }

    cout <<argv[0] << "," << num_cores << "," << exp_time << endl;

    return 0;
}