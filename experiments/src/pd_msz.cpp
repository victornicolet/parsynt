#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define EXPERIMENT_NAME "msz"

using namespace std;
using namespace tbb;


struct ex_struct { bool a; int cs; int ms; };

struct ex_struct_lifted { bool a; int cs; int ms; int bs;};

void pstruct(ex_struct x) {
    cout << "struct | a = " << x.a << "; cs = " << x.cs
         << "; ms = " << x.ms << endl;
}

void pstructl(ex_struct_lifted x) {
    cout << "struct | a = " << x.a << "; cs = " << x.cs
            << "; ms = " << x.ms
            << "; bs = " << x.bs << endl;
}


void print_state(ex_struct seq, ex_struct_lifted lifted, ex_struct prefix) {
    cout << "ERROR: " << endl;
    pstruct(seq);
    pstructl(lifted);
    pstruct(prefix);
}

void seq_implem(const int *A, long start, long end, ex_struct &x) {
    bool a = x.a;
    int ms = x.ms; int cs = x.cs;

    for(long i = start; i < end; i++) {
        int elt = A[i];
        a = a || elt == 0;
        ms = elt == 0 ? max(ms, cs) : ms;
        cs = a && elt != 0 ? cs + elt : 0;
    }
    x.ms = ms; x.cs = cs; x.a =a;
}

void seq_lifted(const int *A, long start, long end, ex_struct_lifted &x) {
    bool a = x.a;
    int ms = x.ms; int cs = x.cs;
    int bs = x.bs;

    for(long i = start; i < end; i++) {
        int elt = A[i];
        a = a || elt == 0;
        ms = elt == 0 ? max(ms, cs) : ms;
        cs = a && elt != 0 ? cs + elt : 0;
        bs = !a ? bs + elt : bs;
    }
    x.ms = ms; x.cs = cs; x.a =a;
    x.bs = bs;
}

void ex_join(ex_struct &lhs, ex_struct rhs) {
    lhs.a = lhs.a || rhs.a;
    lhs.cs = rhs.cs;
    lhs.ms = max(rhs.ms, lhs.ms);
}

void ex_lifted_join(ex_struct_lifted &lhs, ex_struct_lifted rhs) {
    lhs.a = lhs.a || rhs.a;
    lhs.cs = rhs.cs;
    lhs.ms = max(max(rhs.ms, lhs.ms), lhs.cs + rhs.bs);
    lhs.bs = lhs.bs + (!lhs.a ? rhs.bs : 0) ;
}

struct EX_LIFTED {
    int *A;
    ex_struct_lifted res;

    explicit EX_LIFTED(int* _A, long sz) : res((ex_struct_lifted){ false, 0, 0 ,0 }), A(_A) {}

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

    explicit EX_PREFIX(int* _A, long sz) : res((ex_struct){ false, 0, 0}), A(_A), ps(-1), pe(-1) {}

    EX_PREFIX(EX_PREFIX& s, split) { A = s.A; res = s.res; pe = s.pe; ps = s.ps; }

    void operator()( const blocked_range<long>& r ) {
        long i0 = r.begin();
        long iend = r.end();
        if(ps == -1 && i0 > 0) {
            ps = i0;
            pe = i0;
            while( pe < iend && (A[pe] != 0)) {
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
    ex_struct res = (ex_struct) {false, 0,0};
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

double do_par(int* input, long n, int num_cores) {
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

double do_par_prefix(int* input, long n, int num_cores) {
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


bool incorrect(int* A, long n) {
    ex_struct r_seq = (ex_struct) {false, 0,0};
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

    if(r_seq.ms == mbo_par.res.ms && r_seq.ms == mbo_pre.res.ms) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        print_state(r_seq, mbo_par.res, mbo_pre.res);
        return true;
    }

}



int main(int argc, char** argv) {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./ExpMbo SIZE [MAX_CORES]" << endl;
        return  -1;
    }

    int num_cores = EXP_MAX_CORES;

    if(argc >= 3) {
        num_cores = atoi(argv[2]);
    }

    int n = atoi(argv[1]);
    // Data allocation and initialization
    int *input;
    input = create_rand_enum_1D_array(n, 0, 5);
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
            print_result_line(EXPERIMENT_NAME, "lifted", num_threads, n, 0, ref_time, exp_time);
            exp_time = do_par_prefix(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "prefix", num_threads, n, 0, ref_time, exp_time);
        } else {
            // Do the sequential experiment.
            exp_time = do_seq(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq", num_threads, n, 0, ref_time, exp_time);
        }
    }

    return 0;
}
