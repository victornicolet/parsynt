#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define EXPERIMENT_NAME "lmo"

using namespace std;
using namespace tbb;

struct lmo { int cl; int ml; };

struct lmo_lifted {int cl; int sl; int ml; bool cond; };

void seq_implem(int *A, long start, long end, lmo &x) {
    int ml = x.ml;
    int cl = x.cl;

    for(int i = start; i < end; i++) {
        cl = A[i] > 0 ? cl + A[i]: 0;
        ml = max(ml,cl);
    }
    x.ml  = ml;
    x.cl = cl;
}

void seq_lifted(int *A, long start, long end, lmo_lifted &x) {
    int ml = x.ml;
    int cl = x.cl;
    int sl = x.sl;
    bool cond = x.cond;

    for(int i = start; i < end; i++) {
        cond = cond && A[i] > 0;
        sl += cond ? 1: 0;
        cl = A[i]  > 0 ? cl + A[i]: 0;
        ml = max(ml,cl);
    }
    x.ml  = ml;
    x.cl = cl;
    x.sl = sl;
    x.cond = cond;
}

void lmo_join(lmo &lhs, lmo rhs) {
    lhs.ml = max(lhs.ml, rhs.ml);
    lhs.cl = rhs.cl;
}

void lmo_lifted_join(lmo_lifted &lhs, lmo_lifted rhs) {
    lhs.ml = max(lhs.ml, max(lhs.cl + rhs.sl, rhs.ml));
    lhs.cl = rhs.cl;
}

struct EX_LIFTED {
    int *A;
    lmo_lifted res;

    explicit EX_LIFTED(int* _A, long sz) : res((lmo_lifted){0,0,0,true}), A(_A) {}

    EX_LIFTED(EX_LIFTED& s, split) { A = s.A; res = s.res; }

    void operator()( const blocked_range<long>& r ) {
        seq_lifted(A, r.begin(), r.end(), res);
    }

    void join(EX_LIFTED& rhs) {
        lmo_lifted_join(res, rhs.res);
    }
};

struct EX_PREFIX {
    int *A;
    long ps;
    long pe;
    lmo res;

    explicit EX_PREFIX(int* _A, long sz) : res((lmo){0,0}), A(_A), ps(-1), pe(-1) {}

    EX_PREFIX(EX_PREFIX& s, split) { A = s.A; res = s.res; pe = s.pe; ps = s.ps; }

    void operator()( const blocked_range<long>& r ) {
//      Ignore prefix of ones, will be computed in the join with the left state.
        long i0 = r.begin();
        long iend = r.end();
        if(ps == -1 && i0 > 0) {
            ps = i0;
            pe = i0;
            while(pe < iend && A[pe] > 0) {
                pe++;
            }
            i0 = pe;
        }
        seq_implem(A, i0, iend, res);
    }

    void join(EX_PREFIX& rhs) {
        if(rhs.pe > rhs.ps)
            seq_implem(A, rhs.ps, rhs.pe, res);
        lmo_join(res, rhs.res);
    }
};


double do_seq(int *A, long n) {
    lmo res = (lmo) {0,0};
    seq_implem(A, 0, n, res);

    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT; i++) {
        res = (lmo) {0,0};
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

    EX_LIFTED lmo_par(input, n);
    parallel_reduce(blocked_range<long>(0, n-1), lmo_par);

    for(int i = 0; i < NUM_REPEAT ; i++){
        EX_LIFTED lmo_par_x(input, n);
        tbb::static_partitioner pt;
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), lmo_par_x, pt);
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

    EX_PREFIX lmo_par(input, n);
    parallel_reduce(blocked_range<long>(0, n-1), lmo_par);

    for(int i = 0; i < NUM_REPEAT ; i++){
        EX_PREFIX lmo_par_x(input, n);
        tbb::static_partitioner pt;
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), lmo_par_x, pt);
        elapsed += t.stop();
    }

    init.terminate();

    return elapsed / NUM_REPEAT;
}


bool incorrect(int* A, long n) {
    lmo r_seq = (lmo) {0,0};
    seq_implem(A, 0, n, r_seq);
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
//    Naive parallel solution with quadratic join.
    EX_LIFTED lmo_par(A, n);
    tbb::static_partitioner pt;
    parallel_reduce(blocked_range<long>(0, n), lmo_par, pt);
//    Parallel solution with "prefix saving"
    EX_PREFIX lmo_pre(A,n);
    parallel_reduce(blocked_range<long>(0, n), lmo_pre, pt);
    init.terminate();
    if(r_seq.ml == lmo_par.res.ml && r_seq.ml == lmo_pre.res.ml) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        return true;
    }

}



int main(int argc, char** argv) {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./ExpLmo SIZE [MAX_CORES] [DISTRIB] [DISTRIB_BLOCK_SIZE]" << endl;
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
            input = create_rand_int_1D_array(n);
            break;
    }
    // Correctness check.
#ifdef CORRECTNESS_TEST_ON
        if(incorrect(input, n))
            return -1;
#endif

    double ref_time = 1.0;

    for(int num_threads = 1; num_threads <= num_cores; num_threads++) {
        double exp_time = 0.0;

        if (num_threads > 1) {
            // Do the parallel experiment.
            exp_time = do_par_lifted(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "lifted", num_threads, n, block_size, ref_time, exp_time);
            exp_time = do_par_prefix(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "prefix", num_threads, n, block_size, ref_time, exp_time);
        } else {
            // Do the sequential experiment.
            exp_time = do_seq(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq", num_threads, n, block_size, ref_time, exp_time);
        }
    }

    return 0;
}
