#include <tbb/tbb.h>
#include <iostream>
#include <assert.h>
#include "StopWatch.h"
#include "param.h"
#include "datagen.h"

#define  EXPERIMENT_NAME "pop"

using namespace std;
using namespace tbb;

typedef int iter_t;

inline auto optimal(Point p1, Point p2) -> bool {
    return p1.x >= p2.x || p1.y >= p2.y;
}


void seq_implem(Point *A, iter_t start, iter_t end, bool *r) {

    for(iter_t i = start; i < end; i++) {
        Point p = A[i];
        bool is_opt = true;
        for(iter_t j = start; j < end; j++) {
            if (i != j) {
                is_opt = is_opt && optimal(p, A[j]);
            }
        }
        r[i] = is_opt;
    }
}

void join_222(Point *A, iter_t start, iter_t mid, iter_t end, bool* res) {
    iter_t i, j;
    for(i = start; i < end; i++){
        if(res[i]){
            Point p = A[i];
            bool is_opt = true;
            iter_t s0 = i > mid ? 0 : mid + 1;
            iter_t s1 = i > mid ? mid + 1: end;
            for(j = s0; j < s1; j++) {
                is_opt = is_opt && optimal(p, A[j]);
            }
            res[i] = is_opt;
        }
    }
}

#ifdef USE_PARALLEL_REDUCE_IMPLEM
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
                bool is_opt = true;
                for(j = begin; j < rhs.end; j++) {
                    is_opt = is_opt && optimal(p, A[j]);
                }
                r[i] = is_opt;
            }
        }
        end = rhs.end;
    }
};


void soln_222(int r, Point *input, iter_t start, iter_t end, bool* res) {
    Ex222 ex(input, res);
    parallel_reduce(blocked_range<iter_t>(start, end), ex);
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
    for(iter_t i = start; i < end; i++) {
        if(A[i].x + A[i].y > pivot.x + pivot.y || A[i] == pivot) {
            pivot = A[i];
        }
    }
    iter_t _mid = end -1;
    iter_t i = start;
    while(i < _mid){
        if(A[i].y >= pivot.y && A[i].x < pivot.x){
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



void lifted_122(const Point *A, iter_t start, iter_t end, bool *r, double &max_x) {
    double _max_x = max_x;
    for(iter_t i = start; i < end; i++) {
        _max_x = A[i].x > _max_x ? A[i].x : _max_x;
        bool is_opt = true;
        for (iter_t j = start; j < end; j++) {
            if(i != j) {
                is_opt = is_opt && optimal(A[i], A[j]);
            }
        }
        r[i] = is_opt;
    }
    max_x = _max_x;
}

void join_lifted_122(Point *A, iter_t start, iter_t end, bool *r, double max_x) {
    for(iter_t i = start; i < end; i++) {
        if(r[i] && A[i].x < max_x) {
            r[i] = false;
        }
    }
}


void _soln_122(int r, Point *A, iter_t start, iter_t end, bool *res, double &max_x) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        lifted_122(A, start, end, res, max_x);
    } else {
        iter_t mid = 0;
        double max_left = 0.;
        double max_right = 0.;
        partition_122(A, start, end, mid);
        task_group g;
        g.run([&] { _soln_122(r+1, A, start, mid, res, max_left); });
        g.run([&] { _soln_122(r+1, A, mid, end, res, max_right); });
        g.wait();
        join_lifted_122(A, mid, end, res, max_left);
        max_x = max(max_left, max_right);
    }
}

void soln_122(int r, Point *A, iter_t start, iter_t end, bool *res) {
    double max_x = 0;
    _soln_122(r, A, start, end, res, max_x);
}

void _seq_soln_122(int r, Point *A, iter_t start, iter_t end, bool *res, double &max_x) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        lifted_122(A, start, end, res, max_x);
    } else {
        iter_t mid = 0;
        double max_left = 0;
        double max_right = 0;
        partition_122(A, start, end, mid);
        _seq_soln_122(r+1, A, start, mid, res, max_left);
        _seq_soln_122(r+1, A, mid, end, res, max_right);
        join_lifted_122(A, mid, end, res, max_left);
        max_x = max(max_left, max_right);
    }
}

void seq_soln_122(int r, Point *A, iter_t start, iter_t end, bool *res) {
    double max_x = 0;
    _seq_soln_122(r, A, start, end, res, max_x);
}

// SOLUTION = (0,2,3)

void partition_023(Point* A, iter_t start, iter_t end, iter_t &mid1, iter_t &mid2) {
//   Pivot1 selection
    double pmax = A[start].y;
    double pmin = A[start].y;
    for(iter_t j = start; j < end; j++) {
        pmax = max(pmax, A[j].y);
        pmin = min(pmin, A[j].y);
    }
//    double divisor = 2 - (((double) (rand() % 100)) / 100) * (2 - sqrt(2));
    double divisor = sqrt(2);
    double pivot1 = (pmax + pmin) / divisor;
//  Pivot2 selection
    double pivot2 = 0.;
    for(iter_t j = start; j < end; j++){
        pivot2 = A[j].y >= pivot1 ? max(pivot2, A[j].x) : pivot2;
    }

    iter_t _mid1 = start;
    iter_t _mid2 = end - 1;
    iter_t i = start;
    while(i <= _mid2) {
        Point p = A[i];
        if(A[i].y > pivot1){
            swap(A[i], A[_mid1]);
            _mid1++;
            i++;
        } else if (p.x < pivot2){
            swap(A[i], A[_mid2]);
            _mid2--;
        } else {
            i++;
        }
    }
    mid1 = _mid1;
    mid2 = _mid2 + 1;
}


void soln_023(int r, Point *A, iter_t start, iter_t end, bool *res) {
    if(end - start <= PARTITION_MIN || r >= RECURSION_MAX) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid1 = 0;
        iter_t mid2 = 0;
        partition_023(A, start, end, mid1, mid2);
        task_group g;
        g.run([=] { soln_023(r+1, A, start, mid1, res); });
        g.run([=] { soln_023(r+1, A, mid1, mid2, res); });
        g.wait();
    }
}


void seq_soln_023(int r, Point *A, iter_t start, iter_t end, bool *res) {
    if(end - start <= PARTITION_MIN) {
        seq_implem(A, start, end, res);
    } else {
        iter_t mid1 = 0;
        iter_t mid2 = 0;
        partition_023(A, start, end, mid1, mid2);
        if(mid1 <= start + PARTITION_MIN || mid2 <= mid1 + PARTITION_MIN) {
            seq_implem(A, start, mid2, res);
        } else {
            seq_soln_023(r+1, A, start, mid1, res);
            seq_soln_023(r+1, A, mid1, mid2, res);
        }
    }
}


// EXTRA SOLUTION - SORT then PARALLEL
void join_100(const Point *A, bool* res, const iter_t start, const iter_t end, const double max_x) {
    for(iter_t i = start; i < end; i++){
        if(res[i] && A[i].x < max_x)  res[i] = false;
    }
}

void sort_pred100(Point *A, iter_t start, iter_t end){
    struct {
        bool operator()(const Point a, const Point b){
            if (a.y < b.y) {
                return true;
            } else if (a.y == b.y) {
                return a.x >= b.x;
            } else {
                return false;
            }
        }
    } pred100;

    sort((Point*) A + start, (Point*) A + end, pred100);
}


void _soln_100(int r, const Point *A, iter_t start, iter_t end, bool *res, double &max_x){
    if(end - start < PARTITION_MIN || r > RECURSION_MAX) {
        lifted_122(A, start, end, res, max_x);
    } else {
        iter_t mid = (end + start) / 2;
        double max_right = 0;
        double max_left = 0;
        task_group g;
        g.run( [&]{_soln_100(r+1, A, start, mid, res, max_left);});
        g.run( [&]{_soln_100(r+1, A, mid, end, res, max_right);});
        g.wait();
        join_100(A, res, start, mid, max_right);
        max_x = max(max_left, max_right);
    }
}

void soln_100(int r, Point *A, iter_t start, iter_t end, bool *res){
    sort_pred100(A, start, end);
    double max_x = 0;
    _soln_100(0, A, start, end, res, max_x);
}




void _seq_soln_100(int r, const Point *A, iter_t start, iter_t end, bool *res, double &max_x){
    if(end - start < PARTITION_MIN || r > RECURSION_MAX) {
        lifted_122(A, start, end, res, max_x);
    } else {
        iter_t mid = (end + start) / 2;
        double max_right = 0;
        double max_left = 0;
        _seq_soln_100(r+1, A, start, mid, res, max_left);
        _seq_soln_100(r+1, A, mid, end, res, max_right);
        join_100(A, res, start, mid, max_right);
        max_x = max(max_left, max_right);
    }
}

void seq_soln_100(int r, Point *A, iter_t start, iter_t end, bool *res){
    sort_pred100(A, start, end);
    double max_x = 0;
    _seq_soln_100(0, A, start, end, res, max_x);
}


/* WRAPPERS for timing execution ============================================*/
auto do_seq_orig(Point *A, iter_t n) -> double {
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


auto incorrect(Point* A, iter_t n) -> bool {
    cout << "Correctness test." << endl;
    bool* res[7];
    for(auto & re : res){
        re = (bool*) malloc(n*sizeof(bool));
        for(iter_t j = 0; j< n; j++){
            re[j] = false;
        }
    }
    static task_scheduler_init init(task_scheduler_init::deferred);
    init.initialize(CHECK_THREADS_NUM, UT_THREAD_DEFAULT_STACK_SIZE);

    seq_implem(A, 0, n, res[0]);
    soln_222(0,A,0 ,n, res[1]);
    soln_022(0, A, 0, n, res[2]);
    soln_122(0, A, 0, n, res[3]);
    soln_023(0, A, 0, n, res[4]);
    soln_100(0, A, 0, n, res[5]);
    seq_soln_100(0, A, 0, n, res[6]);
    init.terminate();
    iter_t seq_count = 0, par_count = 0, div_count = 0, div_x_count = 0, div_3_count = 0;
    iter_t  sol100_count = 0, seq_sol_100_count = 0;
    for(iter_t i = 0; i < n; i++){
        seq_count += res[0][i];
        par_count += res[1][i];
        div_count += res[2][i];
        div_x_count += res[3][i];
        div_3_count += res[4][i];
        sol100_count += res[5][i];
        seq_sol_100_count += res[6][i];
    }
    for(auto & re : res) {
        free(re);
    }
    if (seq_count == par_count && seq_count == div_count &&
        div_x_count == seq_count && div_3_count == seq_count &&
        sol100_count == seq_count && seq_sol_100_count == seq_count) {
        return false;
    } else {
        cout << "Correctness test failed." << endl;
        cout << "Optimal points:\n seq = " << seq_count << endl
             << " s222 = " << par_count << endl
             << " s022 = " << div_count << endl
             << " s122 = " << div_x_count << endl
             << " s023 = " << div_3_count << endl
             << " s100 = " << sol100_count << endl
             << " s100 (seq) = " << seq_sol_100_count << endl;
        return true;
    }
}



auto main(int argc, char** argv) -> int {
    // Data size:
    if(argc < 2) {
        cout << "Usage:./PtExpPop NUM_POINTS [MAX_THREADS] [OPT_RATIO] [EXPCODE]" << endl;
        cout << "     MAX_THREADS : maximum numbers of threads to run experiment." << endl;
        cout << "     OPT_RATIO : Ratio of optimal points." << endl;
        cout << "     EXPCODE: string of five characters = 0 or 1" << endl;
        cout << "              #1(e222) #2(e022) #3(e122) #4(e023) #5(e100)" << endl;
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
    bool expcode[5] {true, true, true, true, true};
    if(argc >= 5) {
        for(int i = 0; i < 5; i++){
            expcode[i] = argv[4][i] == '1';
        }
    }


    Point *input;
    input = create_stair_distrib_point_1D_array(n, r);

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
                exp_time = do_par<Point, bool, &soln_222>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par222", num_threads, n, delta, ref_time, exp_time);
            }
            if(expcode[1]) {
                exp_time = do_par<Point, bool, &soln_022>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[2]){
                exp_time = do_par<Point, bool, &soln_122>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par122", num_threads, n, delta, ref_time, exp_time);
            }
            if(expcode[3]) {
                exp_time = do_par<Point, bool, &soln_023>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par023", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[4]){
                exp_time = do_par<Point, bool, &soln_100>(input, n, num_threads);
                print_result_line(EXPERIMENT_NAME, "par100", num_threads, n, delta, ref_time, exp_time);
            }
        } else {
            // Do the sequential experiments.
            exp_time = do_seq_orig(input, n);
            ref_time = exp_time;
            print_result_line(EXPERIMENT_NAME, "seq000", num_threads, n, delta, ref_time, exp_time);
            if(expcode[0]) {
                exp_time = do_seq<Point, bool, &seq_soln_222>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq222", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[1]) {
                exp_time = do_seq<Point, bool, &seq_soln_022>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq022", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[2]) {
                exp_time = do_seq<Point, bool, &seq_soln_122>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq122", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[3]) {
                exp_time = do_seq<Point, bool, &seq_soln_023>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq023", num_threads, n, delta, ref_time,
                                  exp_time);
            }
            if(expcode[4]) {
                exp_time = do_seq<Point, bool, &seq_soln_100>(input, n);
                print_result_line(EXPERIMENT_NAME, "seq100", num_threads, n, delta, ref_time,
                                  exp_time);
            }
        }

    }

    free(input);

    return 0;
}