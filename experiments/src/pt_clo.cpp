#include <tbb/tbb.h>
#include <iostream>
#include <assert.h>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define  EXPERIMENT_NAME "clo"

using namespace std;
using namespace tbb;

typedef int iter_t;

inline auto dist(int p1, int p2) -> int {
    return abs(p2 - p1);
}


void seq_implem(const int *A, iter_t start, iter_t end, int &res) {
    if (end - start <= 1) {
        res = 0;
        return;
    }
    int d = res;
    for(iter_t i = start; i < end; i++) {
        int x1 = A[i];
        for(iter_t j = start; j < i; j++) {
            if (i != j) {
                d = min(d, dist(x1, A[j]));
            }
        }
    }
    res = d;
}



void join_222(int *A, iter_t start, iter_t mid, iter_t end, int &res) {
    iter_t i, j;
    int d = res;
    for(i = start; i < mid; i++) {
        for (j = mid; j < end; j++) {
            d = min(d, dist(A[i], A[j]));
        }
    }
    res = d;
}

#ifdef USE_PARALLEL_REDUCE_IMPLEM
struct Ex222 {
    int *A;
    int r;
    iter_t begin, end;

    explicit Ex222(int* _input) : A(_input), begin(-1), end(-1), r(0) {}
    Ex222(Ex222& s, split) {A = s.A; r =s.r; begin =-1; end = -1;}

    void operator()( const blocked_range<iter_t>& range ) {
        iter_t i0 = range.begin();
        iter_t iEnd = range.end();
        if (begin == -1) begin = i0;
        seq_implem(A, i0, iEnd, r);
        end = iEnd;
    }

    void join(Ex222& rhs) {
        iter_t i,j;
        join_222(A, begin, end, rhs.end, r);
        r = min(r, rhs.r);
        end = rhs.end;
    }
};


void soln_222(int r, int *input, iter_t start, iter_t end, int& res) {
    Ex222 ex(input);
    parallel_reduce(blocked_range<iter_t>(start, end), ex);
    res = ex.r;
}

#else

void soln_222(int r, Point* A, iter_t start, iter_t end, bool *res) {
    if((end - start <= PARTITION_MIN) || (r >= RECURSION_MAX)) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = (end + start) / 2;
        task_group g;
        g.run([&]{soln_222(r + 1, A, start, mid + 1, res);});
        g.run([&]{soln_222(r + 1, A, mid + 1, end, res);});
        g.wait();
        join_222(A, start, mid, end, res);
    }
}

#endif

void seq_soln_222(int r, int* A, iter_t start, iter_t end, int& res) {
    if((end - start <= PARTITION_MIN) || (r >= RECURSION_MAX)) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = (end + start) / 2;
        int res2 = res;
        seq_soln_222(r + 1, A, start, mid + 1, res);
        seq_soln_222(r + 1, A, mid + 1, end, res2);
        join_222(A, start, mid, end, res);
        res = min(res2, res);
    }
}

// SOLUTION = (0, 2, 2)
struct lift {
    int d;
    int xmin;
    int xmax;
};


void lifted_implem(const int *A, iter_t start, iter_t end, lift &res) {
    if (end - start <= 1) {
        res = {0, A[start], A[start]};
        return;
    }
    int d = res.d;
    int xmin = res.xmin;
    int xmax = res.xmax;
    for(iter_t i = start; i < end; i++) {
        int x1 = A[i];
        xmin = min(xmin, x1);
        xmax = max(xmax, x1);
        for(iter_t j = start; j < i; j++) {
            if (i != j) {
                d = min(d, dist(x1, A[j]));
            }
        }
    }
    res.d = d;
    res.xmin = xmin;
    res.xmax = xmax;
}

void partition_022(int* A, iter_t start, iter_t end, iter_t &mid) {
//    Pivot selection
    int pivot = A[(start + end) / 2];
    iter_t _mid = end -1;
    iter_t i = start;
    while(i < _mid){
        if(A[i]>= pivot){
            swap(A[i], A[_mid]);
            _mid--;
        } else {
            i++;
        }
    }
    mid = _mid + 1;
}


void soln_022(int r, int *A, iter_t start, iter_t end, lift &res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        lifted_implem(A, start, end, res);
    } else {
        iter_t mid = 0;
        partition_022(A, start, end, mid);
        lift res2 {res.d, res.xmin, res.xmax};
        task_group g;
        g.run([&] { soln_022(r+1, A, start, mid, res); });
        g.run([&] { soln_022(r+1, A, mid, end, res2); });
        g.wait();
        res.d = min(min(res.d, res2.d), dist(res.xmax, res2.xmin));
        res.xmax = res2.xmax;
    }
}

void seq_soln_022(int r, int *A, iter_t start, iter_t end, lift &res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        lifted_implem(A, start, end, res);
    } else {
        iter_t mid = 0;
        lift res2 {res.d, res.xmin, res.xmax};
        partition_022(A, start, end, mid);
        seq_soln_022(r+1, A, start, mid + 1, res2);
        seq_soln_022(r+1, A, mid + 1, end, res);
        res.d = min(min(res.d, res2.d), dist(res.xmax, res2.xmin));
        res.xmax = res2.xmax;
    }
}



/* WRAPPERS for timing execution ============================================*/
auto do_seq_orig(int *A, iter_t n) -> double {
    StopWatch t;
    double elapsed = 0.0;
    int r = INT_MAX;
    seq_implem(A, 0, n, r);

    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        int res = INT_MAX;
        t.start();
        seq_implem(A, 0, n, res);
        elapsed += t.stop();
    }
    return elapsed / NUM_REPEAT_SEQ;
}

// TEMPLATES

template<class I, class O, void (*T)(int, I*,iter_t, iter_t, O &)>
double do_seq(I *input, iter_t n, O & initv) {
    StopWatch t;
    double elapsed = 0.0;
    O r = initv;
    T(0, input, 0, n, r);

    for(int i = 0; i < NUM_REPEAT_SEQ ; i++){
        r = initv;
        t.start();
        T(0, input, 0, n, r);
        elapsed += t.stop();
    }

    return elapsed / NUM_REPEAT_SEQ;
}


template<class I, class O, void (*T)(int, I*,iter_t, iter_t, O&)>
double do_par(I* input, iter_t n, O initv, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    O r = initv;
    T(0, input, 0, n, r);
    init.terminate();

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        r = initv;
        t.start();
        T(0, input, 0, n, r);
        elapsed += t.stop();
        init2.terminate();
    }

    return elapsed / NUM_REPEAT;
}


auto incorrect(int* A, iter_t n) -> bool {
    cout << "Correctness test." << endl;

    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
    int seq_res = INT_MAX;
    seq_implem(A, 0, n, seq_res);
    int soln_222_res = INT_MAX;
    soln_222(0,A,0 ,n, soln_222_res);
    lift soln_022_res {INT_MAX, INT_MAX, INT_MIN};
    soln_022(0, A, 0, n, soln_022_res);
    init.terminate();


    if (seq_res == soln_222_res && seq_res == soln_022_res.d) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        cout << "Minimal distance:\n seq = " << seq_res << endl
             << " s222 = " << soln_222_res << endl
             << " s022 = " << soln_022_res.d << endl;
        return true;
    }
}



auto main(int argc, char** argv) -> int {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./PtExpPop NUM_POINTS [MAX_THREADS] [SWAP_RATIO] [EXPCODE]" << endl;
        cout << "     MAX_THREADS : maximum numbers of threads to run experiment." << endl;
        cout << "     OPT_RATIO : Ratio of optimal points." << endl;
        cout << "     EXPCODE: string of two characters = 0 or 1" << endl;
        cout << "              #1(e222) #2(e022)" << endl;
        return  -1;
    }

    int max_cores = EXP_MAX_CORES;
    iter_t n = atoi(argv[1]);
    double r = 0.3;
    // Maximum number of threads to be used
    if(argc >= 3) max_cores = atoi(argv[2]);
    // Ratio of optimal points
    if(argc >= 4) {
        r = atof(argv[3]);
    }
    // Experiment code
    bool expcode[5] {true, true};
    if(argc >= 5) {
        for(int i = 0; i < 2; i++){
            expcode[i] = argv[4][i] == '1';
        }
    }


    int *input;
    auto swaps = (iter_t)floor(r * n);
    input = create_randswapsort_int_1D_array(n, swaps);

#ifdef CORRECTNESS_TEST_ON
    bool error = false;
    for(int i = 0; i < 4; i++){
        if (incorrect(input, n)) error = true;
    }
    if (error) return -1;
#endif

    int delta = ceil(r * n);
    double ref_time = 1.0;
    cout.precision(3);

    for(int num_threads = 1; num_threads <= max_cores; num_threads++) {
        double exp_time = 0.0;
        int intr = INT_MAX;
        lift liftr {INT_MAX, INT_MAX, INT_MIN};

        if (num_threads > 1) {
            // Do the parallel experiments.
            if(expcode[0]){
                exp_time = do_par<int, int, &soln_222>(input, n, intr, num_threads);
                print_result_line(EXPERIMENT_NAME, "par222", num_threads, n, delta, ref_time, exp_time);
            }
            if(expcode[1]) {
                exp_time = do_par<int, lift, &soln_022>(input, n, liftr, num_threads);
                print_result_line(EXPERIMENT_NAME, "par022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
        } else {
            // Do the sequential experiments.
            exp_time = do_seq_orig(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq000", num_threads, n, delta, ref_time, exp_time);
            if(expcode[0]) {
                exp_time = do_seq<int, int, &seq_soln_222>(input,  n, intr);
                print_result_line(EXPERIMENT_NAME, "seq222", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[1]) {
                exp_time = do_seq<int, lift, &seq_soln_022>(input, n, liftr);
                print_result_line(EXPERIMENT_NAME, "seq022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
        }

    }

    free(input);

    return 0;
}