#include <tbb/tbb.h>
#include <iostream>
#include <list>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"


using namespace std;
using namespace tbb;



void seq_implem(const int  *A, int k, long start, long end, list<int> *r) {
    list<int> list1;
    r->swap(list1);
    for(long i = start; i < end; i++) {
        int a = A[i];
        int cnt = 0;
        list<int> l2;
        bool added = false;

        for(auto &it : list1) {
            if (a < it && cnt < k && !added) {
                l2.push_back(a);
                added = true;
                cnt++;
            }
            if(cnt < k) {
                l2.push_back(it);
                cnt++;
            }
        }

        if (cnt < k && !added) {
            l2.push_back(a);
        }

        __glibcxx_assert(l2.size() <= k);

        list1.swap(l2);
    }
    r->swap(list1);
}



struct KSmallest {
    int *A;
    int k;
    long n;
    list<int> l;

    explicit KSmallest(int* _input, int _k, long _n) : A(_input), n(_n), k(_k) {}
    KSmallest(KSmallest& s, split) { A = s.A; n = s.n; k = s.k; }

    void operator()( const blocked_range<long>& r ) {
        seq_implem(A, k, r.begin(), r.end(), &l);
    }

    void join(KSmallest& rhs) {
        l.merge(rhs.l);
        l.resize(k);
    }
};


double do_seq(const int *A, int k, long n) {
    list<int> r;
    seq_implem(A, k, 0, n, &r);

    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT; i++) {
        t.start();
        list<int> r2;
        seq_implem(A, k, 0, n, &r2);
        elapsed += t.stop();
    }
    return elapsed / NUM_REPEAT;
}

double do_par(int* input, int k, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);

    KSmallest kLargest(input, k , n);
    parallel_reduce(blocked_range<long>(0, n), kLargest);

    for(int i = 0; i < NUM_REPEAT ; i++){
        KSmallest kLargest1(input, k, n);
        t.start();
        parallel_reduce(blocked_range<long>(0, n), kLargest1);
        elapsed += t.stop();
    }

    init.terminate();

    return elapsed / NUM_REPEAT;
}


bool test_incorrect(int* A, int k, long n) {

    if(k > n){
        cerr << "Specify a k smaller than n" << endl;
        return true;
    }

    list<int> r;
    seq_implem(A, k, 0, n, &r);
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
    KSmallest kLargest(A, k, n);
    parallel_reduce(blocked_range<long>(0, n), kLargest);
    init.terminate();

    if(equal(r.begin(), r.end(), kLargest.l.begin())) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        cout << "Sequential: ";
        for (auto &it : r) {
            cout << it << ",";
        }
        cout << endl;
        cout << "Parallel: ";
        for (auto &elt : kLargest.l) {
            cout << elt << ",";
        }
        cout << endl;
        return true;
    }

}



int main(int argc, char** argv) {
    // Data size:
    if(argc < 3) {
        cout << "Usage:./ExpKLarge [K] [NUM_POINTS]" << endl;
        return  -1;
    }

    int k = atoi(argv[1]);
    long n = atoi(argv[2]);
    // Data allocation and initialization
    int *input;
    input = create_rand_int_1D_array(n);
    // Correctness check.

//    if(test_incorrect(input, k, n))
//        return -1;

    for(int num_threads = 1; num_threads <= EXP_MAX_CORES; num_threads++) {
        double exp_time = 0.0;

        if (num_threads > 1) {
            // Do the parallel experiment.
            exp_time = do_par(input, k, n, num_threads);
        } else {
            // Do the sequential experiment.
            exp_time = do_seq(input, k, n);
        }

        cout << "ksmall" << "," << num_threads << "," << exp_time << endl;
    }

    return 0;
}