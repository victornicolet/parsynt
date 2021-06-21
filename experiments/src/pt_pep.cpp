#include <tbb/tbb.h>
#include <iostream>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define  EXPERIMENT_NAME "pep"

using namespace std;
using namespace tbb;

typedef int iter_t;

inline auto optimal1(Point p1, Point p2) -> bool {
    return p1.x >= p2.x || p1.y >= p2.y;
}

inline auto optimal2(Point p1, Point p2) -> bool {
    return p1.x >= p2.x || p1.y <= p2.y;
}


void seq_implem(Point *A, iter_t start, iter_t end, bool *r) {

    for(iter_t i = start; i < end; i++) {
        Point p = A[i];
        bool o1 = true;
        bool o2 = true;
        for(iter_t j = start; j < end; j++) {
            if (i != j) {
                o1 = o1 && optimal1(p, A[j]);
                o2 = o2 && optimal2(p, A[j]);
            }
        }
        r[i] = o1 || o2;
    }
}

struct Ex222 {
    Point *A;
    bool* r;
    iter_t begin, end;

    explicit Ex222(Point* _input, bool* _r) : A(_input), begin(-1), end(-1), r(_r) {}
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
        for(i = begin; i < rhs.end; i++){
            if(r[i]){
                Point p = A[i];
                bool o1 = true;
                bool o2 = true;
                for(j = begin; j < rhs.end; j++) {
                    o1 = o1 && optimal1(p, A[j]);
                    o2 = o2 && optimal2(p, A[j]);
                }
                r[i] = o1 || o2;
            }
        }
        end = rhs.end;
    }
};

void join_222(Point *A, iter_t start, iter_t mid, iter_t end, bool* res) {
    iter_t i, j;
    for(i = start; i < end; i++){
        if(res[i]){
            Point p = A[i];
            iter_t s0 = i > mid ? 0 : mid + 1;
            iter_t s1 = i > mid ? mid + 1: end;
            bool o1 = true;
            bool o2 = true;
            for(j = s0; j < s1; j++) {
                o1 = o1 && optimal1(p, A[j]);
                o2 = o2 && optimal2(p, A[j]);
            }
            res[i] = o1 || o2;
        }
    }
}

void seq_soln_222(int r, Point* A, iter_t start, iter_t end, bool *res) {
    if((end - start <= PARTITION_MIN) || (r >= RECURSION_MAX)) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = (end + start) / 2;
        seq_soln_222(r + 1, A, start, mid + 1, res);
        seq_soln_222(r + 1, A, mid + 1, end, res);
        join_222(A, start, mid, end, res);
    }
}

// SOLUTION = (0, 2, 2)


void partition_022(Point* A, iter_t start, iter_t end, iter_t &mid) {
//    Pivot selection
    Point pivot = A[(start + end) / 2];
    for(iter_t i = start + 1; i < end; i++) {
        if(A[i].x + A[i].y > pivot.x + pivot.y || (A[i].x + A[i].y == pivot.x + pivot.y)) {
            pivot = A[i];
        }
    }
    iter_t _mid = end -1;
    iter_t i = start;
    while(i < _mid){
        if(A[i].y < pivot.y || (A[i].x == pivot.x && A[i].y == pivot.y)){
            swap(A[i], A[_mid]);
            _mid--;
        } else {
            i++;
        }
    }

    mid = _mid + 1;
}


void soln_022(int r, Point *A, iter_t start, iter_t end, bool *res) {
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

void seq_soln_022(int r, Point *A, iter_t start, iter_t end, bool *res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid = 0;
        partition_022(A, start, end, mid);
        seq_soln_022(r+1, A, start, mid + 1, res);
        seq_soln_022(r+1, A, mid + 1, end, res);
    }
}

// SOLUTION = (1,2,2)

void partition_122(Point* A, iter_t start, iter_t end, iter_t &mid) {
//    Pivot selection
    double pmax = A[start].y;
    double pmin = A[start].y;
    for(iter_t j = start; j < end; j++) {
       pmax = max(pmax, A[j].y);
       pmin = min(pmin, A[j].y);
    }
//    double divisor = 2 - (((double) (rand() % 100)) / 100) * (2 - sqrt(2));

    double pivot = (pmax + pmin) / sqrt(2.);
    iter_t _mid = end-1;
    iter_t i = start;
    while(i < _mid){
        if(A[i].y < pivot){
            swap(A[i], A[_mid]);
            _mid--;
        } else {
            i++;
        }
    }
    mid = _mid;
}



void lifted_122(Point *A, iter_t start, iter_t end, bool *r, double &max_x) {
    double _max_x = max_x;
    for(iter_t i = start; i < end; i++) {
        Point p = A[i];
        _max_x = max(A[i].x, _max_x);
        bool o1 = true, o2 = true;
        for (iter_t j = start; j < end; j++) {
            if(i != j) {
                o1 = o1 && optimal1(p, A[j]);
                o2 = o2 && optimal2(p, A[j]);
            }
        }
        r[i] = o1 || o2;
    }
    max_x = _max_x;
}

void join_lifted_122(Point *A, iter_t start, iter_t mid, iter_t end, bool *r, double max_x_l, double max_x_r) {
    for(iter_t i = start; i < end; i++) {
        if(A[i].x <= max_x_l) {
            r[i] = false;
        }
    }
}


void soln_122(int r, Point *A, iter_t start, iter_t end, bool *res, double &max_x) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        lifted_122(A, start, end, res, max_x);
    } else {
        iter_t mid = 0;
        double max_left = 0.;
        double max_right = 0.;
        partition_122(A, start, end, mid);
        task_group g;
        g.run([&] { soln_122(r+1, A, start, mid, res, max_left); });
        g.run([&] { soln_122(r+1, A, mid, end, res, max_right); });
        g.wait();
        join_lifted_122(A, start, mid, end, res, max_left, max_right);
        max_x = max(max_left, max_right);

    }
}

void seq_soln_122(int r, Point *A, iter_t start, iter_t end, bool *res, double &max_x) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        lifted_122(A, start, end, res, max_x);
    } else {
        iter_t mid = 0;
        double max_left = 0;
        double max_right = 0;
        partition_122(A, start, end, mid);
        seq_soln_122(r+1, A, start, mid, res, max_left);
        seq_soln_122(r+1, A, mid, end, res, max_right);
        join_lifted_122(A, start, mid, end, res, max_left, max_right);
        max_x = max(max_left, max_right);
    }
}


// WRAPPERS for timing execution

auto do_seq(Point *A, iter_t n) -> double {
    StopWatch t;
    double elapsed = 0.0;
    bool* r = (bool*) malloc(n*sizeof(bool));

    seq_implem(A, 0, n, r);

    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        bool* rl = (bool*) malloc(n*sizeof(bool));
        t.start();
        seq_implem(A, 0, n, rl);
        elapsed += t.stop();
        free(rl);
    }
    free(r);
    return elapsed / NUM_REPEAT_SEQ;
}

auto do_seq_soln222(Point *A, iter_t n) -> double  {
    StopWatch t;
    double elapsed = 0.0;
    bool* r = (bool*) malloc(n * sizeof(bool));

    seq_soln_222(0, A, 0, n, r);

    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        bool *rl = (bool*) malloc(n * sizeof(bool));
        t.start();
        seq_soln_222(0, A, 0, n, rl);
        elapsed += t.stop();
        free(rl);
    }
    free(r);
    return elapsed / NUM_REPEAT_SEQ;
}


auto do_seq_soln022(Point *A, iter_t n) -> double {
    StopWatch t;
    double elapsed = 0.0;
    bool* r = (bool*) malloc(n*sizeof(bool));

    seq_soln_022(0, A, 0, n, r);

    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        bool* rl = (bool*) malloc(n*sizeof(bool));
        t.start();
        seq_soln_022(0, A, 0, n, rl);
        elapsed += t.stop();
        free(rl);
    }
    free(r);
    return elapsed / NUM_REPEAT_SEQ;
}


auto do_seq_soln122(Point *A, iter_t n) -> double {
    StopWatch t;
    double elapsed = 0.0;
    bool* r = (bool*) malloc(n*sizeof(bool));
    double max_x_1 = 0.;
    seq_soln_122(0, A, 0, n, r, max_x_1);
    free(r);

    for(int i = 0; i < NUM_REPEAT_SEQ; i++) {
        bool* rl = (bool*) malloc(n*sizeof(bool));
        double max_x = 0.;
        t.start();
        seq_soln_122(0, A, 0, n, rl, max_x);
        elapsed += t.stop();
        free(rl);
    }

    return elapsed / NUM_REPEAT_SEQ;
}


auto do_par_soln222(Point *input, iter_t n, int num_cores) -> double {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    bool* r = (bool*) malloc(n * sizeof(bool));
    Ex222 ex(input, r);
    parallel_reduce(blocked_range<iter_t>(0, n), ex);
    init.terminate();
    free(r);

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        bool *r2 = (bool*) malloc(n * sizeof(bool));
        Ex222 ex1(input, r2);
        t.start();
        parallel_reduce(blocked_range<iter_t>(0, n-1), ex1);
        elapsed += t.stop();
        init2.terminate();
        free(r2);
    }


    return elapsed / NUM_REPEAT;
}

auto do_par_soln022(Point *input, iter_t n, int num_cores) -> double {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    bool* r = (bool*) malloc(n * sizeof(bool));
    soln_022(0, input, 0, n, r);
    init.terminate();
    free(r);

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        bool* r2 = (bool*) malloc(n * sizeof(bool));
        t.start();
        soln_022(0, input, 0, n, r2);
        elapsed += t.stop();
        init2.terminate();
        free(r2);
    }

    return elapsed / NUM_REPEAT;
}

auto do_par_soln122(Point *input, iter_t n, int num_cores) -> double {
    StopWatch t;
    double elapsed = 0.0;
    // TBB Initialization with num_cores cores
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    bool* r = (bool*) malloc(n * sizeof(bool));
    double max_x = 0.;
    soln_122(0, input, 0, n, r, max_x);
    init.terminate();
    free(r);

    for(int i = 0; i < NUM_REPEAT ; i++){
        static task_scheduler_init init2(task_scheduler_init::deferred);
        init2.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
        r = (bool*) malloc(n * sizeof(bool));
        double max_x_i = 0.;
        t.start();
        soln_122(0, input, 0, n, r, max_x_i);
        elapsed += t.stop();
        init2.terminate();
        free(r);
    }

    return elapsed / NUM_REPEAT;
}


auto incorrect(Point* A, iter_t n) -> bool {
    cout << "Correctness test." << endl;
    bool* r1 = (bool*) malloc(n*sizeof(bool));
    bool* r2 = (bool*) malloc(n*sizeof(bool));
    bool* r3 = (bool*) malloc(n*sizeof(bool));
    bool* r4 = (bool*) malloc(n*sizeof(bool));
    for(iter_t i = 0; i< n; i++){
        r1[i] = false; r2[i] = false; r3[i] = false; r4[i] = false;
    }
    seq_implem(A, 0, n, r1);
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);
    Ex222 pareto(A,r2);
    parallel_reduce(blocked_range<iter_t>(0, n), pareto);
    soln_022(0, A, 0, n, r3);
    double max_x = 0.;
    soln_122(0, A, 0, n, r4, max_x);
    init.terminate();
    iter_t seq_count = 0, par_count = 0, div_count = 0, div_x_count = 0;
    for(iter_t i = 0; i< n; i++){
        seq_count += r1[i];
        par_count += r2[i];
        div_count += r3[i];
        div_x_count += r4[i];
    }
    free(r1);
    free(r2);
    free(r3);
    free(r4);
    if (seq_count == par_count && seq_count == div_count &&
        div_x_count == seq_count ) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        cout << "Optimal points: seq = " << seq_count <<" s222 = " << par_count
             << " s022 = " << div_count << " s122 = " << div_x_count << endl;
        return true;
    }
}



auto main(int argc, char** argv) -> int {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./PtExpPop NUM_POINTS [MAX_CORES] [OPT_RATIO]" << endl;
        return  -1;
    }

    int max_cores = EXP_MAX_CORES;
    iter_t n = atoi(argv[1]);
    double r = 0.3;

    if(argc >= 3) max_cores = atoi(argv[2]);
    if(argc >= 4) {
        r = atof(argv[3]);
    }


    Point *input;
    input = create_stair_distrib_point_1D_array(n, r);

#ifdef CORRECTNESS_TEST_ON
        if (incorrect(input, n)) return -1;
    #endif

    int delta = ceil(r * n);
    double ref_time = 1.0;
    cout.precision(3);

    for(int num_threads = 1; num_threads <= max_cores; num_threads++) {
        double exp_time = 0.0;

        if (num_threads > 1) {
            // Do the parallel experiments.
            exp_time = do_par_soln222(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "par222", num_threads, n, delta, ref_time, exp_time);
            exp_time = do_par_soln022(input, n, num_threads);
//            print_result_line(EXPERIMENT_NAME, "par022", num_threads, n, delta, ref_time, exp_time);
//            exp_time = do_par_soln122(input, n, num_threads);
            print_result_line(EXPERIMENT_NAME, "par122", num_threads, n, delta, ref_time, exp_time);
        } else {
            // Do the sequential experiments.
            exp_time = do_seq(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq000", num_threads, n, delta, ref_time, exp_time);
            exp_time = do_seq_soln222(input, n);
            print_result_line(EXPERIMENT_NAME, "seq222", num_threads, n, delta, ref_time, exp_time);
            exp_time = do_seq_soln022(input, n);
            print_result_line(EXPERIMENT_NAME, "seq022", num_threads, n, delta, ref_time, exp_time);
            exp_time = do_seq_soln122(input, n);
            print_result_line(EXPERIMENT_NAME, "seq122", num_threads, n, delta, ref_time, exp_time);
        }

    }

    free(input);

    return 0;
}