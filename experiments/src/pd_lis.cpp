#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define EXPERIMENT_NAME "lis"

using namespace std;
using namespace tbb;


struct lis { int cl; int ml; int prev; };

struct lis_lifted {int cl; int sl; int ml; bool cond; int prev; };

void seq_implem(int *A, long start, long end, lis &x) {
    int ml = x.ml;
    int cl = x.cl;
    int prev = x.prev;
    for(int i = start; i < end; i++) {
        cl = A[i] > prev ? cl + 1: 0;
        ml = max(ml,cl);
        prev = A[i];
    }
    x.ml  = ml;
    x.cl = cl;
    x.prev = prev;
}

void seq_lifted(int *A, long start, long end, lis_lifted &x) {
    int ml = x.ml;
    int cl = x.cl;
    int sl = x.sl;
    bool cond = x.cond;
    int prev = x.prev;
    for(int i = start; i < end; i++) {
        cond = cond && A[i] > prev;
        sl += cond ? 1: 0;
        cl = A[i]  > prev ? cl + 1: 0;
        ml = max(ml,cl);
        prev = A[i];
    }
    x.ml  = ml;
    x.cl = cl;
    x.sl = sl;
    x.cond = cond;
    x.prev = prev;
}

void lis_join(lis &lhs, lis rhs) {
    lhs.ml = max(lhs.ml, rhs.ml);
    lhs.cl = rhs.cl;
}

void lis_lifted_join(lis_lifted &lhs, lis_lifted rhs) {
    lhs.ml = max(lhs.ml, max(lhs.cl + rhs.sl, rhs.ml));
    lhs.cl = rhs.cl;
    lhs.prev = rhs.prev;
}

struct LIS {
    int *A;
    lis_lifted res;

    explicit LIS(int* _A, long sz) : res((lis_lifted){0,0,0,true,INT_MIN}), A(_A) {}

    LIS(LIS& s, split) { A = s.A; res = s.res; }

    void operator()( const blocked_range<long>& r ) {
        seq_lifted(A, r.begin(), r.end(), res);
    }

    void join(LIS& rhs) {
        lis_lifted_join(res, rhs.res);
    }
};

struct LIS_PREFIX {
    int *A;
    long ps;
    long pe;
    lis res;

    explicit LIS_PREFIX(int* _A, long sz) : res((lis){0,0}), A(_A), ps(-1), pe(-1) {}

    LIS_PREFIX(LIS_PREFIX& s, split) { A = s.A; res = s.res; pe = -1; ps = -1; }

    void operator()( const blocked_range<long>& r ) {
//      Ignore prefix of ones, will be computed in the join with the left state.
        long i0 = r.begin();
        long iend = r.end();
        if(ps == -1 && i0 > 0) {
            ps = i0;
            pe = i0;
            while(pe < iend && A[pe] < A[pe+1]) {
                pe++;
            }
            i0 = pe;
        }
        seq_implem(A, i0, iend, res);
    }

    void join(LIS_PREFIX& rhs) {
        if(rhs.pe > rhs.ps)
            seq_implem(A, rhs.ps, rhs.pe, res);
        lis_join(res, rhs.res);
    }
};


double do_seq(int *A, long n) {
    lis res = (lis) {0,0, INT_MIN};
    seq_implem(A, 0, n, res);

    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT; i++) {
        res = (lis) {0,0, INT_MIN};
        t.start();
        seq_implem(A, 0, n, res);
        elapsed += t.stop();
    }
    return elapsed / NUM_REPEAT;
}

double do_par_lifted(int *input, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    LIS lis_par(input, n);
    parallel_reduce(blocked_range<long>(0, n-1), lis_par);

    for(int i = 0; i < NUM_REPEAT ; i++){
        LIS lis_par_x(input, n);
        tbb::static_partitioner pt;
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), lis_par_x, pt);
        elapsed += t.stop();
    }

    init.terminate();

    return elapsed / NUM_REPEAT;
}

double do_par_prefix(int* input, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    LIS_PREFIX lis_par(input, n);
    parallel_reduce(blocked_range<long>(0, n-1), lis_par);

    for(int i = 0; i < NUM_REPEAT ; i++){
        LIS_PREFIX lis_par_x(input, n);
        tbb::static_partitioner pt;
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), lis_par_x, pt);
        elapsed += t.stop();
    }

    init.terminate();

    return elapsed / NUM_REPEAT;
}


bool incorrect(int* A, long n) {
    lis r_seq = (lis) {0,0, INT_MIN};
    seq_implem(A, 0, n, r_seq);
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
//    Naive parallel solution with quadratic join.
    LIS lis_par(A, n);
    tbb::static_partitioner pt;
    parallel_reduce(blocked_range<long>(0, n), lis_par, pt);
//    Parallel solution with "prefix saving"
    LIS_PREFIX lis_pre(A,n);
    parallel_reduce(blocked_range<long>(0, n), lis_pre, pt);
    init.terminate();
    if(r_seq.ml == lis_par.res.ml && r_seq.ml == lis_pre.res.ml) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        return true;
    }

}



int main(int argc, char** argv) {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./ExpLis SIZE [MAX_CORES] [DISTRIB] [DISTRIB_BLOCK_SIZE]" << endl;
        return  -1;
    }

    int num_cores = EXP_MAX_CORES;

    if(argc >= 3) {
        num_cores = atoi(argv[2]);
    }
    int use_distrib = 0;
    int block_size = 100;
    if(argc >= 5) {
        use_distrib = atoi(argv[3]);
        block_size = atoi(argv[4]);
    }

    int n = atoi(argv[1]);
    int *input;

    switch(use_distrib) {
        case 1:
            input = create_randblocks_int_1D_array(n, block_size);
            break;
        default:
            input = create_randblocks_int_1D_array(n, block_size);
            break;
    }
    // Correctness check.

#ifdef CORRECTNESS_TEST_ON
        if(incorrect(input, n))
            return -1;
#endif

    double ref_time = 1.0;
    double exp_time = 0.0;

    for(int num_threads = 1; num_threads <= num_cores; num_threads++) {
        if (num_threads > 1) {
            // Do the parallel experiment.
            exp_time = do_par_lifted(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "par0", num_threads, n, block_size, ref_time, exp_time);
            exp_time = do_par_prefix(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "par1", num_threads, n, block_size, ref_time, exp_time);
        } else {
            // Do the sequential experiment.
            exp_time = do_seq(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq0", num_threads, n, block_size, ref_time, exp_time);
        }
    }

    return 0;
}
