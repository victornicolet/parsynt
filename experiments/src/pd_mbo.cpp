#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define EXPERIMENT_NAME "mbo"

using namespace std;
using namespace tbb;


struct ex_struct { int cl; int ml;};

struct ex_struct_lifted {int cl; int sl; int ml; bool cond; };

void seq_implem(bool *A, long start, long end, ex_struct &x) {
    int ml = x.ml;
    int cl = x.cl;
    for(int i = start; i < end; i++) {
        cl = A[i] ? cl + 1: 0;
        ml = max(ml,cl);
    }
    x.ml  = ml;
    x.cl = cl;
}

void seq_lifted(bool *A, long start, long end, ex_struct_lifted &mbo0) {
    int ml = mbo0.ml;
    int cl = mbo0.cl;
    int sl = mbo0.sl;
    bool cond = mbo0.cond;
    for(int i = start; i < end; i++) {
        cond = cond && A[i];
        sl += cond ? 1: 0;
        cl = A[i] ? cl + 1: 0;
        ml = max(ml,cl);
    }
    mbo0.ml  = ml;
    mbo0.cl = cl;
    mbo0.sl = sl;
    mbo0.cond = cond;
}

void ex_join(ex_struct &lhs, ex_struct rhs) {
    lhs.ml = max(lhs.ml, rhs.ml);
    lhs.cl = rhs.cl;
}

void ex_lifted_join(ex_struct_lifted &lhs, ex_struct_lifted rhs) {
    lhs.ml = max(lhs.ml, max(lhs.cl + rhs.sl, rhs.ml));
    lhs.cl = rhs.cl;
}

struct EX_LIFTED {
    bool *A;
    long n;
    ex_struct_lifted res;

    explicit EX_LIFTED(bool* _A, long sz) : res((ex_struct_lifted){0,0,0,true}), A(_A) {}

    EX_LIFTED(EX_LIFTED& s, split) { A = s.A; res = s.res; }

    void operator()( const blocked_range<long>& r ) {
        seq_lifted(A, r.begin(), r.end(), res);
    }

    void join(EX_LIFTED& rhs) {
        ex_lifted_join(res, rhs.res);
    }
};

struct EX_PREFIX {
    bool *A;
    long ps;
    long pe;
    ex_struct res;

    explicit EX_PREFIX(bool* _A, long sz) : res((ex_struct){0,0}), A(_A), ps(-1), pe(-1) {}

    EX_PREFIX(EX_PREFIX& s, split) { A = s.A; res = s.res; pe = s.pe; ps = s.ps; }

    void operator()( const blocked_range<long>& r ) {
//      Ignore prefix of ones, will be computed in the join with the left state.
        long i0 = r.begin();
        long iend = r.end();
        if(ps == -1 && i0 > 0) {
            ps = i0;
            pe = i0;
            while( pe < iend && A[pe]) {
                pe++;
            }
            i0 = pe;
        }
        seq_implem(A, i0, iend, res);
    }

    void join(EX_PREFIX& rhs) {
        if(rhs.pe > rhs.ps)
            seq_implem(A, rhs.ps, rhs.pe, res);
        ex_join(res, rhs.res);
    }
};


double do_seq(bool *A, long n) {
    ex_struct res = (ex_struct) {0,0};
    seq_implem(A, 0, n, res);

    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT; i++) {
        res = (ex_struct) {0,0};
        t.start();
        seq_implem(A, 0, n, res);
        elapsed += t.stop();
    }
    return elapsed / NUM_REPEAT;
}

double do_par(bool* input, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    EX_LIFTED mbo_par(input, n);
    parallel_reduce(blocked_range<long>(0, n-1), mbo_par);

    for(int i = 0; i < NUM_REPEAT ; i++){
        EX_LIFTED mbo_par_x(input, n);
        tbb::static_partitioner pt;
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), mbo_par_x, pt);
        elapsed += t.stop();
    }

    init.terminate();

    return elapsed / NUM_REPEAT;
}

double do_par_prefix(bool* input, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    EX_PREFIX mbo_par(input, n);
    parallel_reduce(blocked_range<long>(0, n-1), mbo_par);

    for(int i = 0; i < NUM_REPEAT ; i++){
        EX_PREFIX mbo_par_x(input, n);
        tbb::static_partitioner pt;
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), mbo_par_x, pt);
        elapsed += t.stop();
    }

    init.terminate();

    return elapsed / NUM_REPEAT;
}


bool incorrect(bool* A, long n) {
    ex_struct r_seq = (ex_struct) {0,0};
    seq_implem(A, 0, n, r_seq);
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
//    Naive parallel solution with quadratic join.
    EX_LIFTED mbo_par(A, n);
    tbb::static_partitioner pt;
    parallel_reduce(blocked_range<long>(0, n), mbo_par, pt);
//    Parallel solution with "prefix saving"
    EX_PREFIX mbo_pre(A,n);
    parallel_reduce(blocked_range<long>(0, n), mbo_pre, pt);
    init.terminate();

    if(r_seq.ml == mbo_par.res.ml && r_seq.ml == mbo_pre.res.ml) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        return true;
    }

}



int main(int argc, char** argv) {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./ExpMbo SIZE [MAX_CORES] [DISTRIB] [DISTRIB_BLOCK_SIZE]" << endl;
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
    // Data allocation and initialization
    bool *input;

    switch(use_distrib) {
        case 1:
            input = create_randblocks_bool_1D_array(n, block_size);
            break;
        default:
            input = create_rand_bool_1D_array(n);
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
            exp_time = do_par(input, n, num_threads);
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
