#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"
#include "omp.h"
#include "assert.h"
#include <list>

#define EXPERIMENT_NAME "his"

using namespace std;
using namespace tbb;

typedef int iter_t;

typedef struct  ex_lifted { bool b; Point l; Point r; } ex_lifted;


void seq_implem(IDPair *A, iter_t start, iter_t end, IDPair* hist, iter_t hist_start, iter_t& hlen) {
    iter_t _hlen = hlen;
    for(iter_t i = start; i < end; i++) {
        IDPair x = A[i];
        bool added = false;

        for (iter_t j = hist_start; j < hist_start + _hlen; j++){
            IDPair y = hist[j];
            if(y.kind == x.kind){
                hist[j] = {x.kind, x.quant + y.quant};
                added = true;
            }
        }
        if(!added){
            hist[hist_start + _hlen] = x;
            _hlen++;
        }
    }
    hlen = _hlen;
}

void join222(IDPair* histogram, iter_t lhs_start, iter_t& hlen, const iter_t rhs_start, const iter_t rhs_hlen) {
    iter_t _hlen = hlen;
    for(iter_t i = 0; i < rhs_hlen; i++) {
        IDPair x = histogram[rhs_start + i];
        bool added = false;
        for (iter_t j = 0; j < _hlen; j++){
            IDPair y = histogram[lhs_start + j];
            if(y.kind == x.kind){
                histogram[lhs_start + j] = {x.kind, x.quant + y.quant};
                added = true;
            }
        }
        if(!added){
            histogram[lhs_start + _hlen] = x;
            _hlen++;
        }
    }
    hlen = _hlen;
}


struct Ex222 {
    IDPair *A;
    iter_t n;
    IDPair* histogram;
    iter_t histogram_length;
    iter_t begin, end;

    explicit Ex222(IDPair* _input, IDPair* _histogram, iter_t _n) : A(_input), begin(-1), end(-1), n(_n) {
        histogram = _histogram;
        histogram_length = 0;
    }

    Ex222(Ex222& s, split) {
        A = s.A; begin =-1; end = -1;
        n = s.n;
        histogram = s.histogram;
        histogram_length = 0;
    }

    void operator()( const blocked_range<iter_t>& range ) {
        iter_t i0 = range.begin();
        iter_t iEnd = range.end();
        if (begin == -1) begin = i0;
        seq_implem(A, i0, iEnd, histogram, begin, histogram_length);
        end = iEnd;
    }

    void join(Ex222& rhs) {
        assert(histogram_length + rhs.histogram_length <= n);
        join222(histogram, begin, histogram_length, rhs.begin, rhs.histogram_length);
    }
};

double do_par_soln222(IDPair *input, iter_t n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    auto hist = (IDPair*)malloc(n*sizeof(IDPair));
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    Ex222 ex(input, hist, n);
    parallel_reduce(blocked_range<iter_t>(0, n), ex);
    init.terminate();

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        Ex222 ex1(input, hist, n);
        t.start();
        parallel_reduce(blocked_range<iter_t>(0, n-1), ex1);
        elapsed += t.stop();
        init2.terminate();
    }
    free(hist);
    return elapsed / NUM_REPEAT;
}

void seq_soln_222(int r, IDPair *A, iter_t start, iter_t end, IDPair* R, iter_t& hlen) {
    if(r >  RECURSION_MAX || (end - start) <= PARTITION_MIN) {
        seq_implem(A, start, end, R, start, hlen);
    } else {
        iter_t mid = (start + end) / 2;
        seq_soln_222(r+1, A, start, mid + 1, R, hlen);
        iter_t rhs_hlen = 0;
        seq_soln_222(r+1, A, mid + 1, end, R, rhs_hlen);
        join222(R, start, hlen, mid + 1, rhs_hlen);
    }
}

double do_seq_soln222(IDPair *input, iter_t n) {
    StopWatch t;
    double elapsed = 0.0;
    auto R = (IDPair*)malloc(n * sizeof(IDPair));
    iter_t hlen = 0;
    seq_soln_222(0, input, 0, n, R, hlen);

    for(int i = 0; i < NUM_REPEAT_SEQ ; i++){
        auto R2 = (IDPair*)malloc(n * sizeof(IDPair));
        iter_t hlen2 = 0;
        t.start();
        seq_soln_222(0, input, 0, n, R2, hlen2);
        elapsed += t.stop();
        free(R2);
    }
    free(R);
    return elapsed / NUM_REPEAT_SEQ;
}


void partition_022(IDPair* A, iter_t start, iter_t end, iter_t &mid) {
    int pivot = A[start].kind;
    iter_t _mid = end;
    iter_t i = start;
    while(i <= _mid){
        if(A[i].kind > pivot) {
            swap(A[i], A[_mid]);
            _mid--;
        } else {
            i++;
        }
    }
    mid = _mid;
}


void join022(IDPair* R, const iter_t lhs_start, iter_t& hlen, const iter_t rhs_start, iter_t rhs_hlen) {
    for(iter_t i = hlen; i < hlen + rhs_hlen; i++){
        R[lhs_start + i] = R[rhs_start + i - hlen];
    }
    hlen += rhs_hlen;
}


void soln_022(int r, IDPair *A, iter_t start, iter_t end, IDPair* R, iter_t& hlen) {
    if((end - start) <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(A, start, end, R, start, hlen);
    } else {
        iter_t mid = end-1;
        partition_022(A, start, end, mid);
        task_group g;
        g.run([&] { soln_022(r+1, A, start, mid, R, hlen); });
        iter_t rhs_hlen = 0;
        g.run([&] { soln_022(r+1, A, mid, end, R, rhs_hlen); });
        g.wait();
        join022(R, start, hlen, mid, rhs_hlen);
    }
}

void seq_soln_022(int r, IDPair *A, iter_t start, iter_t end, IDPair* R, iter_t& hlen) {
    if((end - start) <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(A, start, end, R, start, hlen);
    } else {
        iter_t mid = start;
        partition_022(A, start, end, mid);
        seq_soln_022(r+1, A, start, mid, R, hlen);
        iter_t rhs_hlen = 0;
        seq_soln_022(r+1, A, mid, end, R, rhs_hlen);
        assert(mid + rhs_hlen <= end);
        join022(R, start, hlen, mid, rhs_hlen);
    }
}


double do_par_soln022(IDPair *input, iter_t n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    auto R = (IDPair*)malloc(n * sizeof(IDPair));
    iter_t hlen = 0;
    soln_022(0, input, 0, n, R, hlen);
    init.terminate();
    free(R);

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        auto R2 = (IDPair*)malloc(n * sizeof(IDPair));
        iter_t hlen2 = 0;
        t.start();
        soln_022(0, input, 0, n, R2, hlen2);
        elapsed += t.stop();
        init2.terminate();
        free(R2);
    }
    return elapsed / NUM_REPEAT;
}


double do_seq_soln022(IDPair *input, iter_t n) {
    StopWatch t;
    double elapsed = 0.0;
    auto R = (IDPair*)malloc(n * sizeof(IDPair));
    iter_t hlen = 0;
    seq_soln_022(0, input, 0, n, R, hlen);
    free(R);

    for(int i = 0; i < NUM_REPEAT_SEQ ; i++){
        auto R2 = (IDPair*)malloc(n * sizeof(IDPair));
        iter_t hlen2 = 0;
        t.start();
        seq_soln_022(0, input, 0, n, R2, hlen2);
        elapsed += t.stop();
        free(R2);
    }
    return elapsed / NUM_REPEAT_SEQ;
}


double do_seq(IDPair *A, iter_t n) {
    auto R = (IDPair*)malloc(n * sizeof(IDPair));
    iter_t hlen = 0;
    seq_implem(A, 0, n, R, 0, hlen);
    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        t.start();
        seq_implem(A, 0, n, R, 0, hlen);
        elapsed += t.stop();
    }
    free(R);

    return elapsed / NUM_REPEAT_SEQ;
}


bool incorrect(IDPair* A, iter_t n) {
    cout << "Correctness test ..." << endl;
    auto his = (IDPair*)malloc(n * sizeof(IDPair));
    iter_t hlen = 0;
    seq_implem(A, 0, n, his, 0, hlen);
    //  Divide-and-conquer solution.
    //  TBB version
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
    auto his2 = (IDPair*)malloc(n * sizeof(IDPair));
    Ex222 ex(A, his2, n);
    parallel_reduce(blocked_range<iter_t>(0, n-1), ex);
    init.terminate();

    auto his3 = (IDPair*)malloc(n * sizeof(IDPair));
    iter_t hlen3 = 0;
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
    soln_022(0, A, 0, n, his3, hlen3);
    init.terminate();

    free(his);
    free(his2);
    free(his3);

    if(hlen3 - 1 == hlen && ex.histogram_length == hlen) {
        cout << "Correctness test succeeded." << endl;
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        cout << "Seq size:" << hlen << endl;
        cout << "S222 size:" << ex.histogram_length << endl;
        cout << "S022 size:" << hlen3 << endl;
        return true;
    }
}

//#define CORRECTNESS_TEST_ON

int main(int argc, char** argv) {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./PtExpHis NUM_POINTS [NUM_THREADS] [NUM_CLASSES] [EXPCODE]" << endl;
        cout << "                 NUM_POINTS: number of data points in input." << endl;
        cout << "       optional NUM_THREADS: maximum number of threads used." << endl;
        cout << "       optional CLASS_RATIO: number of classes in histogram." << endl;
        cout << "       optional     EXPCODE: experiment code, two 0s or 1s  " << endl;
        cout << "                             #1: B = (2,2,2)                " << endl;
        cout << "                             #2: B = (0,2,2)                " << endl;
        return  -1;
    }

    long n = atoi(argv[1]);

    int num_cores = EXP_MAX_CORES;
    if(argc >= 3) {
        num_cores = atoi(argv[2]);
    }
    // Number of classes
    double class_ratio = 0.1;
    if(argc >= 4) {
        class_ratio = atof(argv[3]);
    }
    int num_kinds = (int) floor(class_ratio * n);
    // Experiment code
    bool expcode[2] {true, true};
    if(argc >= 5) {
        for(int i = 0; i < 2; i++){
            expcode[i] = argv[4][i] == '1';
        }
    }

    // Data allocation and initialization
    IDPair *input = create_hist_array(n, num_kinds);

    cout.precision(3);
    // Correctness check.
#ifdef CORRECTNESS_TEST_ON
        if (incorrect(input, n)) return -1;
#endif

    double ref_time = 1.0;
    double exp_time;

    for(int num_threads = 1; num_threads <= num_cores; num_threads++) {
        if (num_threads > 1) {
            // Do the parallel experiments.
            if(expcode[0]){
                exp_time = do_par_soln222(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par222", num_threads, n, num_kinds, ref_time, exp_time);
            }
            if(expcode[1]) {
                exp_time = do_par_soln022(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par022", num_threads, n, num_kinds, ref_time, exp_time);
            }
        } else {
            // Do the sequential experiment.
            exp_time = do_seq(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq000", num_threads, n, num_kinds, ref_time, exp_time);
            if(expcode[0]){
                exp_time = do_seq_soln222(input, n);
                print_result_line(EXPERIMENT_NAME, "seq222", num_threads, n, num_kinds, ref_time, exp_time);
            }
            if(expcode[1]){
                exp_time = do_seq_soln022(input,  n);
                print_result_line(EXPERIMENT_NAME, "seq022", num_threads, n, num_kinds, ref_time, exp_time);
            }
        }
    }
    return 0;
}