#include <tbb/tbb.h>
#include <iostream>
#include <cassert>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define  EXPERIMENT_NAME "kla"

using namespace std;
using namespace tbb;

typedef int iter_t;

struct kla_input {
    int *A;
    int k;
};

struct kla_res {
    int *r;
    int knt;
};

void seq_implem(const kla_input I, iter_t start, iter_t end, int *r) {
    int *tmp = (int*)malloc(I.k * sizeof(int));
    iter_t _k0 = 0;
    iter_t cnt = 0;
    for(iter_t i = start; i < end; i++) {
        int x = I.A[i];
        bool added = false;
        cnt = 0;
        for(iter_t j = 0; j < _k0; j++) {
            int y = r[j];
            if(y > x && !added && cnt < I.k) {
                tmp[cnt] = x;
                added = true;
                cnt++;
            }
            if(cnt < I.k){
                tmp[cnt] = y;
                cnt++;
            }
        }
        // cnt = _k0 || cnt = _k0 + 1
        if(!added && cnt < I.k) {
            tmp[cnt] = x;
            cnt++;
        }
        _k0 = cnt;
        assert(_k0 <= I.k);
        // _k0' = min(_k0 + 2, k - 1)
        for(iter_t j = 0; j < _k0; j++)
            r[j] = tmp[j];
    }
    free(tmp);
}


void join_222(const kla_input I, int* r, const int *l) {
    int *tmp = (int*)malloc(I.k * sizeof(int));
    iter_t i,i1,i2;
    i1 = 0;
    i2 = 0;
    int val = 0;
    for(i = 0; i < I.k; i++) {
        if ((r[i1] <= l[i2] || i2 >= I.k) && i1 < I.k) {
            val = r[i1];
            i1++;
        } else {
            val = l[i2];
            i2++;
        }
        tmp[i] = val;
    }
    for(i = 0; i < I.k; i++)
        r[i] = tmp[i];
    free(tmp);
}


#ifdef USE_PARALLEL_REDUCE_IMPLEM
struct Ex222 {
    kla_input A;
    int* r;
    iter_t begin, end;

    explicit Ex222(kla_input _input) : A(_input), begin(-1), end(-1) {
        r = (int*) malloc(A.k * sizeof(int));
    }
    Ex222(Ex222& s, split) {A = s.A; begin =-1; end = -1; r = (int*) malloc(A.k * sizeof(int));}

    void operator()( const blocked_range<iter_t>& range ) {
        iter_t i0 = range.begin();
        iter_t iEnd = range.end();
        if (begin == -1) begin = i0;
        seq_implem(A, i0, iEnd, r);
    }

    void join(Ex222& rhs) {
        join_222(A, r, rhs.r);
    }
};


void soln_222(int r, kla_input input, iter_t start, iter_t end, int* res) {
    Ex222 ex(input);
    parallel_reduce(blocked_range<iter_t>(start, end), ex);
    for(iter_t i = 0; i < input.k; i++)
        res[i] = ex.r[i];
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

void seq_soln_222(int r, const kla_input A, iter_t start, iter_t end, int *res) {
    if((end - start <= PARTITION_MIN) || (r >= RECURSION_MAX)) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = (end + start) / 2;
        seq_soln_222(r + 1, A, start, mid + 1, res);
        int* tmp_res = (int*) malloc(A.k * sizeof(int));
        seq_soln_222(r + 1, A, mid + 1, end, tmp_res);
        join_222(A, res, tmp_res);
        free(tmp_res);
    }
}

// SOLUTION = (0, 2, 2)


void partition_022(kla_input I, iter_t start, iter_t end, iter_t &mid) {
    int pivot = I.A[(start + end) / 2];
    iter_t _mid = end -1;
    iter_t i = start;
    while(i <= _mid){
        if(I.A[i] >= pivot){
            swap(I.A[i], I.A[_mid]);
            _mid--;
        } else {
            i++;
        }
    }
    mid = _mid;
}


void soln_022(int r, kla_input I, iter_t start, iter_t end, int *res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(I, start, end, res);
    } else {
        iter_t mid = 0;
        partition_022(I, start, end, mid);
        task_group g;
        g.run([=] { soln_022(r+1, I, start, mid, res); });
        int* tmp_res = (int*)malloc(I.k * sizeof(int));
        g.run([=] { soln_022(r + 1, I, mid + 1, end, tmp_res); });
        g.wait();
        for(iter_t i = mid - start + 1; i < I.k; i++) {
            res[i] = tmp_res[i - (mid - start + 1)];
        }
        free(tmp_res);
    }
}

void seq_soln_022(int r, kla_input A, iter_t start, iter_t end, int *res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = 0;
        partition_022(A, start, end, mid);
        seq_soln_022(r+1, A, start, mid + 1, res);
        if(mid - start < A.k) {
            int *tmp_res = (int *) malloc(A.k * sizeof(int));
            seq_soln_022(r + 1, A, mid + 1, end, tmp_res);
            for(iter_t i = mid - start + 1; i < A.k; i++) {
                res[i] = tmp_res[i - (mid - start + 1)];
            }
            free(tmp_res);
        }
    }
}



/* WRAPPERS for timing execution ============================================ */
auto do_seq_orig(kla_input A, iter_t n) -> double {
    StopWatch t;
    double elapsed = 0.0;
    int* r = (int*) malloc(A.k * sizeof(int));
    seq_implem(A, 0, n, r);
    free(r);

    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        int* rl = (int*) malloc(A.k * sizeof(int));
        t.start();
        seq_implem(A, 0, n, rl);
        elapsed += t.stop();
        free(rl);
    }

    return elapsed / NUM_REPEAT_SEQ;
}

// TEMPLATES

template<class I, class O, void (*T)(int, I,iter_t, iter_t, O*)>
double do_seq(I input, iter_t n) {
    StopWatch t;
    double elapsed = 0.0;
    O* r = (O*) malloc(input.k * sizeof(O));
    T(0, input, 0, n, r);
    free(r);

    for(int i = 0; i < NUM_REPEAT_SEQ ; i++){
        r = (O*) malloc(input.k * sizeof(O));
        t.start();
        T(0, input, 0, n, r);
        elapsed += t.stop();
        free(r);
    }

    return elapsed / NUM_REPEAT_SEQ;
}


template<class I, class O, void (*T)(int, I,iter_t, iter_t, O*)>
double do_par(I input, iter_t n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    O* r = (O*) malloc(input.k * sizeof(O));
    T(0, input, 0, n, r);
    init.terminate();
    free(r);

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        r = (O*) malloc(input.k * sizeof(O));
        t.start();
        T(0, input, 0, n, r);
        elapsed += t.stop();
        init2.terminate();
        free(r);
    }

    return elapsed / NUM_REPEAT;
}


auto incorrect(const kla_input I, iter_t n) -> bool {
    cout << "Correctness test." << endl;
    int* res[3];
    for(auto & re : res){
        re = (int*) malloc(I.k * sizeof(int));
        for(iter_t j = 0; j < I.k; j++){
            re[j] = 0;
        }
    }
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
    seq_implem(I, 0, n, res[0]);
    seq_soln_222(0, I,0 , n, res[1]);
    seq_soln_022(0, I, 0, n, res[2]);

    init.terminate();
    bool seq_ok = true;
    bool soln_222_ok = true;
    bool soln_022_ok = true;
    for(iter_t i = 0; i < I.k - 1; i++) {
        seq_ok &= res[0][i] <= res[0][i + 1];
        soln_222_ok &= res[1][i] <= res[1][i + 1];
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
    if(argc < 3) {
        cout << "Usage:./PtExpSor NUM_POINTS [MAX_THREADS] [K-RATIO] [EXPCODE]" << endl;
        cout << "     MAX_THREADS : maximum numbers of threads to run experiment." << endl;
        cout << "     RATIO : Ratio of k." << endl;
        cout << "     EXPCODE = string of two 0 or 1s" << endl;
        cout << "              #1(e222) #2(e022)" << endl;
        return  -1;
    }

    int max_cores = EXP_MAX_CORES;
    iter_t n = atoi(argv[1]);

    // Maximum number of threads to be used
    if(argc >= 3) max_cores = atoi(argv[2]);

    // Ratio
    double r = 0.3;
    if(argc >= 4) {
        r = atof(argv[3]);
    }
    iter_t k = (iter_t) floor(r * n);

    // Experiment code
    bool expcode[2] {true, true};
    if(argc >= 5) {
        for(int i = 0; i < 2; i++){
            expcode[i] = argv[4][i] == '1';
        }
    }

    iter_t numswaps = max(n, n /  2);



#ifdef CORRECTNESS_TEST_ON
    bool error = false;
    for(int i = 0; i < 4; i++){
        int *input_A;
        input_A = create_randswapsort_int_1D_array(n, numswaps);
        kla_input input { input_A,  k };
        if (incorrect(input, n)) error = true;
    }
    if (error) return -1;
#endif

    int *input_A;
    input_A = create_randswapsort_int_1D_array(n, numswaps);

    kla_input input { input_A,  k };
    int delta = ceil(r * n);
    double ref_time = 1.0;
    cout.precision(3);

    for(int num_threads = 1; num_threads <= max_cores; num_threads++) {
        double exp_time = 0.0;

        if (num_threads > 1) {
            // Do the parallel experiments.
            if(expcode[0]){
                exp_time = do_par<kla_input, int, &soln_222>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par222", num_threads, n, delta, ref_time, exp_time);
            }
            if(expcode[1]) {
                exp_time = do_par<kla_input, int, &soln_022>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
        } else {
            // Do the sequential experiments.
            exp_time = do_seq_orig(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq000", num_threads, n, delta, ref_time, exp_time);
            if(expcode[0]) {
                exp_time = do_seq<kla_input, int, &seq_soln_222>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq222", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[1]) {
                exp_time = do_seq<kla_input, int, &seq_soln_022>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
        }

    }
    //free(input_A);
    return 0;
}