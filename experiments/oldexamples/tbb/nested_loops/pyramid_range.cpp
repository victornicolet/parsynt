#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;


struct Pyramid {
    int **A;
    long m;

    int high, h, low, l;
    int aux_incl44, aux_incl45;
    bool incl;

    Pyramid(int** _input, long rl) : A(_input), m(rl),
                                      high(INT_MAX), h(INT_MAX), low(INT_MIN), l(INT_MIN),
                                      incl(true){}

    Pyramid(Pyramid& s, split) {
        high = INT_MAX; h = INT_MAX;
        low = INT_MIN; l = INT_MIN;
        incl = true;
        A = s.A;
        m = s.m;
    }

    void operator()( const blocked_range<long>& r ) {

        long e = r.begin();

        for(long i = e; i != r.end(); ++i) {
            low = 0;
            high = 0;

            for(long j = 0; j < m; j++) {
                high = max(high, A[i][j]);
                low = min(low, A[i][j]);
            }

            if (i == e) {
                aux_incl44 = high;
                aux_incl45 = low;
            }

            if(!(high <= h) || !(low >= l)) {
                incl = false;
            }

            h = high;
            l = low;

        }
    }

    void join(Pyramid& r) {
        low = r.low;
        high = r.high;
        l = r.l;
        h = r.h;
        incl = (r.aux_incl44 >= h) ? false : ((aux_incl45 <= r.l) ? (r.incl && incl) : false);
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

    Pyramid pv(input, m);

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