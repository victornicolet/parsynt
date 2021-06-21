#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define EXPERIMENT_NAME "ins"

using namespace std;
using namespace tbb;

typedef int iter_t;

typedef struct  ex_lifted { int cnt; Point l; Point r; } ex_lifted;

auto intersect(Point p1, Point p2) -> bool {
    return (p1.x <= p2.x && p2.x <= p1.y) || (p2.x <= p1.x && p1.x <= p2.y);
}

int seq_implem(Point *A, iter_t start, iter_t end) {
    int inters = 0;

    for(long i = start; i < end; i++) {
        Point p = A[i];
        for(long j = i; j < end; j++) {
            inters += intersect(p, A[j]);
        }
    }

    return inters;
}


void partition_022(Point* A, iter_t start, iter_t end, iter_t &mid) {
//    Pivot selection
    Point pivot = A[(end + start) / 2];
    iter_t _mid = end -1;
    iter_t i = start;
    while(i <= _mid){
        if(A[i].x > pivot.y) {
            swap(A[i], A[_mid]);
            _mid--;
        } else {
            i++;
        }
    }
    mid = _mid;
 }

ex_lifted seq_lifted_022(Point *A, iter_t start, iter_t end) {
    int inters = 0;
    Point l = {INT_MAX, INT_MAX};
    Point r = {INT_MIN, INT_MIN};
    for(iter_t i = start; i < end; i++) {
        Point p = A[i];
        l = A[i].x < l.x ? A[i] : l;
        r = A[i].y > r.y ? A[i] : r;
        for(long j = i; j < end; j++) {
            inters  += intersect(p, A[j]);
        }
    }

    return {inters, l, r};
}


ex_lifted join_022(ex_lifted left, ex_lifted right) {
    int b = left.cnt + right.cnt + (intersect(left.r, right.l) ? 0 : 1);
    return {b, left.l, right.r};
}


void soln_022(int r, Point *A, iter_t start, iter_t end, ex_lifted &b) {
    if(end - start <= 500) {
        b = seq_lifted_022(A, start, end);
    } else {
        iter_t mid = -1;
        partition_022(A, start, end, mid);
        if(mid != start && mid != end && r < RECURSION_MAX) {
            ex_lifted b1 = (ex_lifted) {false, (Point) {INT_MAX, INT_MAX}, (Point) {INT_MIN, INT_MIN}};
            ex_lifted b2 = (ex_lifted) {false, (Point) {INT_MAX, INT_MAX}, (Point) {INT_MIN, INT_MIN}};
            task_group g;
            g.run([&] { soln_022(r + 1, A, start, mid, b1); });
            g.run([&] { soln_022(r + 1, A, mid, end, b2); });
            g.wait();
            b = join_022(b1, b2);
        } else {
            b = seq_lifted_022(A, start, end);
        }

    }
}


void seq_soln022(int r, Point *A, iter_t start, iter_t end, ex_lifted &b) {
    if(end - start <= 500) {
        b = seq_lifted_022(A, start, end);
    } else {
        iter_t mid = -1;
        partition_022(A, start, end, mid);
        if(mid != start && mid != end) {
            ex_lifted b1 = (ex_lifted) {false, (Point) {INT_MAX, INT_MAX}, (Point) {INT_MIN, INT_MIN}};
            ex_lifted b2 = (ex_lifted) {false, (Point) {INT_MAX, INT_MAX}, (Point) {INT_MIN, INT_MIN}};
            seq_soln022(r + 1 , A, start, mid, b1);
            seq_soln022(r + 1, A, mid, end, b2);
            b = join_022(b1, b2);
        } else {
            b = seq_lifted_022(A, start, end);
        }
    }
}


/*
 * SOLUTION with Budget = (0,3,3)
 */

void partition_023(Point* A, iter_t start, iter_t end, iter_t &mid1, iter_t &mid2) {
    Point pivot = A[(start + end) / 2];
    swap(A[(start + end)/ 2], A[start]);
    iter_t _mid1 = start + 1;
    iter_t _mid2 = end - 1;
    iter_t i = start + 1;
    while(i <= _mid2) {
        Point p = A[i];
        if(intersect(p, pivot)){
            swap(A[i], A[_mid1]);
            _mid1++;
            i++;
        } else if (p.y < pivot.x){
            swap(A[i], A[_mid2]);
            _mid2--;
        } else {
            i++;
        }
    }
    mid1 = _mid1;
    mid2 = _mid2 + 1;
}

void seq_soln033(int r, Point *A, iter_t start, iter_t end, int &b) {
    if(end - start <= 500 || r > RECURSION_MAX) {
        b = seq_implem(A, start, end);
    } else {
        iter_t mid1 = -1;
        iter_t mid2 = -1;
        partition_023(A, start, end, mid1, mid2);
        int b0 = 0;
        int b1 = 0;
        int b2 = 0;
        if(mid1 - start > 1) {
            seq_soln033(r+1, A, start, mid1, b0);
        }
        if(mid2- mid1 > 0)
            seq_soln033(r+1, A, mid1, mid2, b1);
        if(end - mid2 > 0)
            seq_soln033(r+1, A, mid2, end, b2);

        b = b + b1 + b2 + b0;
    }
}

void soln_033(int r, Point *A, iter_t start, iter_t end, bool &b) {
    if(end - start <= 500 || r > RECURSION_MAX) {
        b = seq_implem(A, start, end);
    } else {
        iter_t mid1, mid2;
        partition_023(A, start, end, mid1, mid2);
        if(mid1 - start > 1) {
            b = true;
//            g.run([&] { soln_033(A, start, mid1, b0); });
        } else {
            bool b1 = false;
            bool b2 = false;
            task_group g;
            if(mid2 - mid1 > 0)
                g.run([&] { soln_033(r+1, A, mid1, mid2, b1); });
            if(end - mid2 > 0)
                g.run([&] { soln_033(r+1, A, mid2, end, b2); });
            g.wait();
            b = b || b1 || b2;
        }
    }
}

double do_seq(Point *A, long n) {
    seq_implem(A, 0, n);

    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        t.start();
        seq_implem(A, 0, n);
        elapsed += t.stop();
    }
    return elapsed / NUM_REPEAT_SEQ;
}


double do_seq_lifted022(Point *A, long n) {
    seq_implem(A, 0, n);

    StopWatch t;
    double elapsed = 0.0;
    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        t.start();
        seq_lifted_022(A, 0, n);
        elapsed += t.stop();
    }
    return elapsed / NUM_REPEAT_SEQ;
}


double do_seq_soln033(Point *input, iter_t n) {
    StopWatch t;
    double elapsed = 0.0;

    int b = 0;
    seq_soln033(0, input, 0, n, b);

    for(int i = 0; i < NUM_REPEAT_SEQ ; i++){
        int b2 = 0;
        t.start();
        seq_soln033(0, input, 0, n, b2);
        elapsed += t.stop();
    }

    return elapsed / NUM_REPEAT_SEQ;
}

double do_seq_soln022(Point *input, long n) {
    StopWatch t;
    double elapsed = 0.0;
    ex_lifted b = (ex_lifted) {false, (Point) {INT_MAX,INT_MAX}, (Point) {INT_MIN,INT_MIN}};
    seq_soln022(0, input, 0, n, b);

    for(int i = 0; i < NUM_REPEAT_SEQ ; i++){
        ex_lifted b2 = (ex_lifted) {false, (Point) {INT_MAX,INT_MAX}, (Point) {INT_MIN,INT_MIN}};
        t.start();
        seq_soln022(0, input, 0, n, b2);
        elapsed += t.stop();
    }

    return elapsed / NUM_REPEAT_SEQ;
}


double do_par_soln022(Point *input, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    ex_lifted b = (ex_lifted) {false, (Point) {INT_MAX,INT_MAX}, (Point) {INT_MIN,INT_MIN}};
    soln_022(0, input, 0, n, b);
    init.terminate();

    for(int i = 0; i < NUM_REPEAT ; i++){
        ex_lifted b2 = (ex_lifted) {false, (Point) {INT_MAX,INT_MAX}, (Point) {INT_MIN,INT_MIN}};
        init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        t.start();
        soln_022(0, input, 0, n, b2);
        elapsed += t.stop();
        init.terminate();
    }

    return elapsed / NUM_REPEAT;
}


double do_par_soln033(Point *input, long n, int num_cores) {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    bool b = false;
    soln_033(0, input, 0, n, b);
    init.terminate();

    for(int i = 0; i < NUM_REPEAT ; i++){
        bool b2 = false;
        init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        t.start();
        soln_033(0, input, 0, n, b2);
        elapsed += t.stop();
        init.terminate();
    }

    return elapsed / NUM_REPEAT;
}


bool incorrect(Point* A, long n) {
    bool b_seq;
    b_seq = seq_implem(A, 0, n);
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
//    Divide-and-conquer solution.
//  TBB version
    bool b_tbb = false;
    soln_033(0, A, 0, n, b_tbb);
    init.terminate();

    if(b_tbb == b_seq) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        return true;
    }
}


int main(int argc, char** argv) {
    // Data size:
    if(argc < 2) {
         cout << "Usage:./PtExpCins NUM_POINTS [NUM_THREADS] [NUM_INTERS]" << endl;
        return  -1;
    }

    int num_cores = EXP_MAX_CORES;
    int n = atoi(argv[1]);
    if(argc >= 3) {
        num_cores = atoi(argv[2]);
    }
    int num_inters = n / 2;
    if(argc >= 4) {
        num_inters = atoi(argv[3]);
    }


    // Data allocation and initialization
    Point *input = create_segment_1D_array_cinter(n, 2 * n, num_inters);

    cout.precision(10);
    // Correctness check.
#ifdef CORRECTNESS_TEST_ON
        if (incorrect(input, n)) {
            free(input);
            return -1;
        }
#endif

    double ref_time = 1.0;
    double exp_time;

    for(int num_threads = 1; num_threads <= num_cores; num_threads++) {
        if (num_threads > 1) {
            // Do the parallel experiments.
            exp_time = do_par_soln022(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "par022", num_threads, n, num_inters, ref_time, exp_time);
            exp_time = do_par_soln033(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "par033", num_threads, n, num_inters, ref_time, exp_time);
        } else {
            // Do the sequential experiment.
            exp_time = do_seq(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq000", num_threads, n, num_inters, ref_time, exp_time);
            exp_time = do_seq_lifted022(input, n);
            print_result_line(EXPERIMENT_NAME, "seq111", num_threads, n, num_inters, ref_time, exp_time);
            exp_time = do_seq_soln022(input, n);
            print_result_line(EXPERIMENT_NAME, "seq022", num_threads, n, num_inters, ref_time, exp_time);
            exp_time = do_seq_soln033(input, n);
            print_result_line(EXPERIMENT_NAME, "seq033", num_threads, n, num_inters, ref_time, exp_time);
        }
    }

    free(input);

    return 0;
}