#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define EXPERIMENT_NAME "cott"

using namespace std;
using namespace tbb;


struct ex_struct { bool a; bool b; int count; };

struct ex_struct_lifted { bool a; bool b; bool d; bool cj; int count; };

void seq_implem(int *A, long start, long end, ex_struct &x) {
    bool a = x.a;
    bool b = x.b;
    int count  = x.count;

    for(long i = start; i < end; i++) {
        int elt = A[i];
        count += elt == 3 && (a || b) ? 1 : 0;
        b = elt == 2;
        a = elt == 1;
    }
    x.b = b;
    x.a = a;
    x.count = count;
}

void seq_lifted(int *A, long start, long end, ex_struct_lifted &x) {
    bool a = x.a;
    bool b = x.b;
    bool d = x.d;
    bool cj = x.cj;
    int count  = x.count;

    for(long i = start; i < end; i++) {
        int elt = A[i];
        count += elt == 2 && (a || b) ? 1 : 0;
        b = elt == 2;
        a = elt == 1;
        d = cj ? elt == 3 : d;
        cj = cj && elt == 2;
    }
    x.b = b; x.a = a; x.d = d; x.cj = cj; x.count = count;
}

void ex_join(ex_struct &lhs, ex_struct rhs) {
    lhs.a = rhs.a;
    lhs.b = rhs.b;
    lhs.count = lhs.count + rhs.count;
}

void ex_lifted_join(ex_struct_lifted &lhs, ex_struct_lifted rhs) {
    lhs.a = rhs.a; lhs.b = rhs.b;
    lhs.cj = lhs.cj && rhs.cj; lhs.d = lhs.d;
    lhs.count = lhs.count + rhs.count + (rhs.d && (lhs.a || lhs.b) ? 1 : 0);
}

struct EX_LIFTED {
    int *A;
    ex_struct_lifted res;

    explicit EX_LIFTED(int* _A, long sz) : res((ex_struct_lifted){false,false, false, true, 0}), A(_A) {}

    EX_LIFTED(EX_LIFTED& s, split) { A = s.A; res = s.res; }

    void operator()( const blocked_range<long>& r ) {
        seq_lifted(A, r.begin(), r.end(), res);
    }

    void join(EX_LIFTED& rhs) {
        ex_lifted_join(res, rhs.res);
    }
};

struct EX_PREFIX {
    int *A;
    long ps;
    long pe;
    ex_struct res;

    explicit EX_PREFIX(int* _A, long sz) : res((ex_struct){false,false, 0}), A(_A), ps(-1), pe(-1) {}

    EX_PREFIX(EX_PREFIX& s, split) { A = s.A; res = s.res; pe = s.pe; ps = s.ps; }

    void operator()( const blocked_range<long>& r ) {
        long i0 = r.begin();
        long iend = r.end();
        if(ps == -1 && i0 > 0) {
            ps = i0;
            pe = i0;
            while(pe < iend && (A[pe] == 1 || A[pe] == 2)) {
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


double do_seq(int *A, long n) {
    ex_struct res = (ex_struct) {false,false,0};
    seq_implem(A, 0, n, res);

    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT; i++) {
        res = (ex_struct) {false, false, 0};
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

    EX_PREFIX ex_par(input, n);
    parallel_reduce(blocked_range<long>(0, n-1), ex_par);

    for(int i = 0; i < NUM_REPEAT ; i++){
        EX_PREFIX ex_par_x(input, n);
        tbb::static_partitioner pt;
        t.start();
        parallel_reduce(blocked_range<long>(0, n-1), ex_par_x, pt);
        elapsed += t.stop();
    }

    init.terminate();

    return elapsed / NUM_REPEAT;
}


bool incorrect(int* A, long n) {
    ex_struct r_seq = (ex_struct) { false, false, 0};
    seq_implem(A, 0, n, r_seq);
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
//    Naive parallel solution with quadratic join.
    EX_LIFTED ex_par(A, n);
    tbb::static_partitioner pt;
    parallel_reduce(blocked_range<long>(0, n), ex_par, pt);
//    Parallel solution with "prefix saving"
    EX_PREFIX lmo_pre(A,n);
    parallel_reduce(blocked_range<long>(0, n), lmo_pre, pt);
    init.terminate();
    if(r_seq.count == lmo_pre.res.count) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        return true;
    }

}



int main(int argc, char** argv) {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./ExpCott SIZE [MAX_CORES]" << endl;
        return  -1;
    }

    int num_cores = EXP_MAX_CORES;

    if(argc >= 3) {
        num_cores = atoi(argv[2]);
    }

    int n = atoi(argv[1]);
    int *input;

    input = create_rand_enum_1D_array(n, 0, 6);

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
            print_result_line(EXPERIMENT_NAME, "lifted", num_threads, n, 0, ref_time, exp_time);
            exp_time = do_par_prefix(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "prefix", num_threads, n, 0, ref_time, exp_time);
        } else {
            // Do the sequential experiment.
            exp_time = do_seq(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "lifted", num_threads, n, 0, ref_time, exp_time);
        }
    }


    return 0;
}
