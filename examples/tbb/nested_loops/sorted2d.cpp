#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"

using namespace std;
using namespace tbb;

static int __min_int = static_cast<int>(INT64_MIN);
static int __max_int = static_cast<int>(INT64_MAX);

struct Sorted2D {
    int **A;
    bool sorted;
    int prev;
    int first;
    long m;

    Sorted2D(int** _input, long rl) :
            A(_input), m(rl), sorted(true), prev(__max_int), first(__min_int){}

    Sorted2D(Sorted2D& s, split) {
        sorted = true;
        prev = __max_int;
        first = __min_int;
        A = s.A;
        m = s.m;
    }

    void operator()( const blocked_range<long>& r ) {
        bool bl = sorted;
        int loc_prev = prev;
        for(long i = r.begin(); i != r.end(); ++i) {
            for(long j = 0; j < m-1; j++) {
                bl = bl && loc_prev > A[i][j];
                loc_prev = A[i][j];
            }
        }
        first =
        prev = loc_prev;
        sorted = bl;
    }

    void join(Sorted2D& rhs) {
        sorted = sorted && rhs.sorted && rhs.prev > first;
        first = rhs.first;
    }

};

double do_seq(int **A, long m, long n) {
    StopWatch t;
    t.start();
    bool b;

    for(long i = 0; i < n - 1; ++i) {
        for(long j = 0; j < m-1; j++) {
            b = b &&
                (A[i+1][j] > A[i][j]) &&
                (A[i][j+1] > A[i][j]);
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

    Gradient1 gr(input, m);

    for(int i = 0; i < NUM_EXP ; i++){
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), gr);
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