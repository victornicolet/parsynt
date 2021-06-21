#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define  EXPERIMENT_NAME "sor"

using namespace std;
using namespace tbb;

typedef int iter_t;


void seq_implem(const int *A, iter_t start, iter_t end, int *r) {
    int *tmp = (int*)malloc((end - start) * sizeof(int));
    for(iter_t i = start; i < end; i++) {
        int x = A[i];
        int k = 0;
        bool added = false;
        for(iter_t j = start; j < i; j++) {
            int y = r[j];
            if(y > x && !added) {
                tmp[k] = x;
                tmp[k+1] = y;
                k+= 2;
                added = true;
            } else {
                tmp[k] = y;
                k++;
            }
        }
        if(!added) {
            tmp[k] = x;
        }
        for(iter_t j = start; j <= i; j++)
            r[j] = tmp[j - start];
    }
    free(tmp);
}


void join_122(int *A, iter_t start, iter_t mid, iter_t end, int* r) {
    int *tmp = (int*)malloc((end - start) * sizeof(int));
    iter_t i,i1,i2;
    i1 = start;
    i2 = mid;
    int val = 0;
    for(i = start; i < end; i++) {
        if ((r[i1] <= r[i2] || i2 >= end) && i1 < mid) {
            val = r[i1];
            i1++;
        } else {
            val = r[i2];
            i2++;
        }
        tmp[i - start] = val;
    }
    for(i = start; i < end; i++)
        r[i] = tmp[i - start];
    free(tmp);
}


#ifdef USE_PARALLEL_REDUCE_IMPLEM
struct Ex122 {
    int *A;
    int* r;
    iter_t begin, end;

    explicit Ex122(int* _input, int* _r) : A(_input), begin(-1), end(-1), r(_r) {}
    Ex122(Ex122& s, split) {A = s.A; r =s.r; begin =-1; end = -1;}

    void operator()( const blocked_range<iter_t>& range ) {
        iter_t i0 = range.begin();
        iter_t iEnd = range.end();
        if (begin == -1) begin = i0;
        seq_implem(A, i0, iEnd, r);
        end = iEnd;
    }

    void join(Ex122& rhs) {
        join_122(A, begin, rhs.begin, rhs.end, r);
        end = rhs.end;
    }
};


void soln_122(int r, int *input, iter_t start, iter_t end, int* res) {
    Ex122 ex(input, res);
    parallel_reduce(blocked_range<iter_t>(start, end), ex);
}

#else

void soln_222(int r, int* A, iter_t start, iter_t end, int *res) {
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

void seq_soln_122(int r, int* A, iter_t start, iter_t end, int *res) {
    if((end - start <= PARTITION_MIN) || (r >= RECURSION_MAX)) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = (end + start) / 2;
        seq_soln_122(r + 1, A, start, mid + 1, res);
        seq_soln_122(r + 1, A, mid + 1, end, res);
        join_122(A, start, mid + 1, end, res);
    }
}

// SOLUTION = (0, 2, 2)


void partition_022(int* A, iter_t start, iter_t end, iter_t &mid) {
    int pivot = A[end-1];
    iter_t _mid = end -1;
    iter_t i = start;
    while(i <= _mid){
        if(A[i] >= pivot){
            swap(A[i], A[_mid]);
            _mid--;
        } else {
            i++;
        }
    }
    mid = _mid;
}


void soln_022(int r, int *A, iter_t start, iter_t end, int *res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = 0;
        partition_022(A, start, end, mid);
        task_group g;
        g.run([=] { soln_022(r+1, A, start, mid, res); });
        g.run([=] { soln_022(r+1, A, mid, end, res); });
        g.wait();
    }
}

void seq_soln_022(int r, int *A, iter_t start, iter_t end, int *res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = 0;
        partition_022(A, start, end, mid);
        seq_soln_022(r+1, A, start, mid + 1, res);
        seq_soln_022(r+1, A, mid + 1, end, res);
    }
}



/* WRAPPERS for timing execution ============================================*/
auto do_seq_orig(int *A, iter_t n) -> double {
    StopWatch t;
    double elapsed = 0.0;
    int* r = (int*) malloc(n*sizeof(int));

    seq_implem(A, 0, n, r);

    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        int* rl = (int*) malloc(n*sizeof(int));
        t.start();
        seq_implem(A, 0, n, rl);
        elapsed += t.stop();
        free(rl);
    }
    free(r);
    return elapsed / NUM_REPEAT_SEQ;
}

// TEMPLATES

template<class I, class O, void (*T)(int, I*,iter_t, iter_t, O*)>
double do_seq(I *input, iter_t n) {
    StopWatch t;
    double elapsed = 0.0;
    O* r = (O*) malloc(n * sizeof(O));
    T(0, input, 0, n, r);
    free(r);

    for(int i = 0; i < NUM_REPEAT_SEQ ; i++){
        r = (O*) malloc(n * sizeof(O));
        t.start();
        T(0, input, 0, n, r);
        elapsed += t.stop();
        free(r);
    }

    return elapsed / NUM_REPEAT_SEQ;
}


template<class I, class O, void (*T)(int, I*,iter_t, iter_t, O*)>
double do_par(I* input, iter_t n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    O* r = (O*) malloc(n * sizeof(O));
    T(0, input, 0, n, r);
    init.terminate();
    free(r);

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        r = (O*) malloc(n * sizeof(O));
        t.start();
        T(0, input, 0, n, r);
        elapsed += t.stop();
        init2.terminate();
        free(r);
    }

    return elapsed / NUM_REPEAT;
}


auto incorrect(int* A, iter_t n) -> bool {
    cout << "Correctness test." << endl;
    int* res[3];
    for(auto & re : res){
        re = (int*) malloc(n*sizeof(int));
        for(iter_t j = 0; j< n; j++){
            re[j] = 0;
        }
    }
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);

    seq_implem(A, 0, n, res[0]);
    seq_soln_122(0,A,0 ,n, res[1]);
    seq_soln_022(0, A, 0, n, res[2]);
    init.terminate();
    bool seq_ok = true;
    bool soln_222_ok = true;
    bool soln_022_ok = true;
    for(iter_t i = 0; i < n-1; i++){
        seq_ok &= res[0][i] <= res[0][i+1];
        soln_222_ok &= res[1][i] <= res[1][i+1];
        soln_022_ok &= res[2][i] <= res[2][i+1];
    }
    for(auto & re : res) {
        free(re);
    }
    if (seq_ok && soln_022_ok && soln_222_ok) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        cout << "Sorted?:\n seq = " << seq_ok << endl
             << " s222 = " << soln_222_ok << endl
             << " s022 = " << soln_022_ok << endl;
        return true;
    }
}



auto main(int argc, char** argv) -> int {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./PtExpSor NUM_POINTS [MAX_THREADS] [RATIO] [EXPCODE]" << endl;
        cout << "     MAX_THREADS : maximum numbers of threads to run experiment." << endl;
        cout << "     RATIO : Ratio of swapped points." << endl;
        cout << "     EXPCODE = string of two 0 or 1s" << endl;
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
    bool expcode[2] {true, true};
    if(argc >= 5) {
        for(int i = 0; i < 2; i++){
            expcode[i] = argv[4][i] == '1';
        }
    }


    int *input;
    iter_t numswaps = max(n, (iter_t) floor(r * n));
    input = create_randswapsort_int_1D_array(n, numswaps);


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

        if (num_threads > 1) {
            // Do the parallel experiments.
            if(expcode[0]){
                exp_time = do_par<int, int, &soln_122>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par122", num_threads, n, delta, ref_time, exp_time);
            }
            if(expcode[1]) {
                exp_time = do_par<int, int, &soln_022>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
        } else {
            // Do the sequential experiments.
            exp_time = do_seq_orig(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq000", num_threads, n, delta, ref_time, exp_time);
            if(expcode[0]) {
                exp_time = do_seq<int, int, &seq_soln_122>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq122", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[1]) {
                exp_time = do_seq<int, int, &seq_soln_022>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
        }

    }

    free(input);

    return 0;
}