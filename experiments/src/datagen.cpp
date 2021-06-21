//
// Created by victorn on 22/10/18.
//
#include <iostream>
#include <iomanip>
#include <cmath>
#include <functional>
#include <limits.h>
#include <random>

#include "param.h"
#include "omp.h"
#include "datagen.h"


using namespace std;

void print_result_line(const string &experiment_name, const string &method,
        int num_threads, int n, int r, double ref_time, double exp_time) {
    cout << setw(PRINT_WIDTH) << left << experiment_name << ","
         << setw(PRINT_WIDTH) << right << method   << ","
         << setw(15) << right << n << ","
         << setw(PRINT_WIDTH) << right << r << ","
         << setw(PRINT_WIDTH) << right << num_threads << ","
         << setw(PRINT_WIDTH) << right << exp_time << ","
         << setw(PRINT_WIDTH) << right << ref_time / exp_time
         << endl;
}

int** create_rand_int_2D_matrix(long m, long n) {
    int** input;

    input = (int**) malloc(n * sizeof(int*));

    for(long i = 0; i < n; i++) {
        input[i] = (int*) malloc(m * sizeof(int));
    }


#pragma omp parallel for
    for(long i = 0; i < n; i++) {
        std::mt19937 rng;
        rng.seed(std::random_device()());
        std::uniform_int_distribution<std::mt19937::result_type> dist122(0, 255);
        for(long j =0; j < m; j++){
            input[i][j] =  (int)dist122(rng) - 122;
        }
    }

    return input;
}


int* create_rand_int_1D_array(long n) {
    int* input;

    input = (int*) malloc(n * sizeof(int));

    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_int_distribution<std::mt19937::result_type> dist122(0, 543);

    for(long i = 0; i < n; i++) {
        input[i] =  (int)dist122(rng) - 255;
    }

    return input;
}

int* create_randswapsort_int_1D_array(long n, long swaps) {
    int* input;

    input = (int*) malloc(n * sizeof(int));
    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_int_distribution<std::mt19937::result_type> distn(0, n);

    for(long i = 0; i < n; i++) {
        input[i] =  (int)distn(rng);
    }

    long step = n / swaps;
    for(long i = 0; i < min(swaps, n); i += step) {
        long j = (long)distn(rng) % (n / 2);
        long a = n / 2 - i;
        long xi = abs(a);
        long xj = min(abs(n / 2 + j - 1), n);
        swap(input[xi], input[xj]);
    }


    return input;
}


float* create_randclo_int_1D_array(long n, long swaps) {
    float* input;

    input = (float*) malloc(n * sizeof(float));

    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_int_distribution<std::mt19937::result_type> distn(0, n);

    for(long i = 0; i < n; i++) {
        input[i] =  (int)distn(rng);
    }
    long step = n / swaps;

    for(long i = 0; i < n; i += step) {
        long j = (long)distn(rng) % n;
        int tmp = input[i];
        input[i] = input[j];
        input[j] = tmp;
    }

    return input;
}

int* create_rand_enum_1D_array(long n, int lo, int hi) {
    int* input;

    input = (int*) malloc(n * sizeof(int));

    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_int_distribution<std::mt19937::result_type> dist122(lo, hi);

    for(long i = 0; i < n; i++) {
        input[i] =  (int)dist122(rng);
    }

    return input;
}

int*** create_rand_int_3D_matrix(long l, long m, long n) {
    int*** input;

    input = (int***) malloc(n * sizeof(int**));

    for(long i = 0; i < n; i++) {
        input[i] = (int**) malloc(m * sizeof(int*));

        for(long j = 0; j< m; j++) {
            input[i][j] = (int*) malloc(l * sizeof(int));
        }
    }

#pragma omp parallel for
    for(long i = 0; i < n; i++) {
        std::mt19937 rng;
        rng.seed(std::random_device()());
        std::uniform_int_distribution<std::mt19937::result_type> dist122(0, 255);
        for(long j =0; j < m; j++){
            for(long k =0; k < l; k++) {
                input[i][j][k] = (int) dist122(rng) - 122;
            }
        }
    }

    return input;
}

bool* create_rand_bool_1D_array(long n){
    bool* A;
    A = (bool*) malloc(n * sizeof(bool));

    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_int_distribution<std::mt19937::result_type> dist122(0, 255);

    for(long i = 0; i < n; i++) {
        A[i] = ((int) dist122(rng) - 122) > 0;
    }

    return A;
}


int* create_randblocks_int_1D_array(long n, int avg_blocksize){
    int* A;
    A = (int*) malloc(n * sizeof(int));

    int block_min = avg_blocksize / 2;

    mt19937 rng;
    rng.seed(random_device()());
    uniform_int_distribution<std::mt19937::result_type> dist122(block_min, avg_blocksize);
    bool blockval = false;
    int blocksize;
    int step;
    A[0] = 0;
    long i = 1, j = 0;
    while(i<n){
        blocksize = (int) dist122(rng);
        for(j = i; j < min(i + blocksize, n); j++) {
            A[j] = blockval ? A[j-1] + 1 : A[j-1] - 1;
        }
        i = j + 1;
        blockval = !blockval;
    }

    return A;
}



bool* create_randblocks_bool_1D_array(long n, int avg_blocksize){
    bool* A;
    A = (bool*) malloc(n * sizeof(bool));

    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_int_distribution<std::mt19937::result_type> dist122(0, avg_blocksize*2);
    long i = 0, j = 0;
    bool blockval = false;
    int blocksize = 1;

    while(i<n){
        blocksize = (int) dist122(rng);
        for(j = i; j < min(i + blocksize, n); j++) {
            A[j] = blockval;
        }
        i = j + 1;
        blockval = !blockval;
    }

    return A;
}


bool** create_rand_bool_2D_matrix(long m, long n){
    bool** A;
    A = (bool**) malloc(n * sizeof(bool*));
    for(long i =0; i < n; i++) {
        A[i] = (bool*) malloc(sizeof(bool) * m);
    }

#pragma omp parallel for
    for(long i = 0; i < n; i++) {
        std::mt19937 rng;
        rng.seed(std::random_device()());
        std::uniform_int_distribution<std::mt19937::result_type> dist122(0, 255);
        for(long j =0; j < m; j++){
            A[i][j] = ((int) dist122(rng) - 122) > 0;
        }
    }

    return A;
}

Point* create_rand_point_1D_array(long n){
    Point* A;
    A = (Point*) malloc(n * sizeof(Point));

#pragma omp parallel for
    for(long i = 0; i < n; i++) {
        std::mt19937 rng;
        rng.seed(std::random_device()());
        std::uniform_real_distribution<double> dist122(0, 99999);
        A[i].x = dist122(rng);
        A[i].y = dist122(rng);
    }

    return A;
}



Point* create_rand_segment_1D_array(long n, int max_value){
    Point* A;
    A = (Point*) malloc(n * sizeof(Point));

#pragma omp parallel for
    for(long i = 0; i < n; i++) {
        std::mt19937 rng;
        rng.seed(std::random_device()());
        std::uniform_real_distribution<double> dist122(0, max_value);

        double x = dist122(rng);
        double y = dist122(rng);
        if (x < y) { A[i].x = x; A[i].y = y;
        } else { A[i].x = y; A[i].y = x; }
    }

    return A;
}

Point* create_segment_1D_array_cinter(int n, int max_value, int num_inters){
    Point* A;
    A = (Point*) malloc(n * sizeof(Point));

    double step = (1.0 * max_value) / (1.0 * n);

    if(num_inters > 0) {
        int inters[num_inters];
        std::mt19937 rng;
        rng.seed(std::random_device()());
        std::uniform_int_distribution<std::mt19937::result_type> dist122(0, n - 1);
        for (int i = 0; i < num_inters; i++) {
            inters[i] = (int) dist122(rng);
        }
        int i0 = inters[0];
        int k = 1;
        bool on = true;
        for (int i = 0; i < n; i++) {
            if (on && i == i0) {
                A[i].x = (i + 0.2) * step;
                A[i].y = (i + 1.2) * step;
                i0 = inters[k];
                k++;
                on = k < num_inters;
            } else {
                A[i].x = (i + 0.2) * step;
                A[i].y = (i + 0.6) * step;
            }
        }
    } else {
        for (int i = 0; i < n; i++) {
            A[i].x = (i + 0.2) * step;
            A[i].y = (i + 0.6) * step;
        }
    }
//     SHUFFLE
    for (int i = 0; i < (n - 1) / 2; i++) {
        int j = i + rand() / (RAND_MAX / (n - i) + 1);
        swap(A[i], A[j]);
    }

    return A;
}

Point* create_rand_point_1D_array_circular(int n, int lo, int hi){
    Point* A;
    A = (Point*) malloc(n * sizeof(Point));
    int nchunks = n / CHUNK_SIZE_RAND_REUSE + 1;
    mt19937 rng0;
    rng0.seed(random_device()());
    uniform_int_distribution<int> rad_hi(hi - (hi - lo) / nchunks, hi);
    double angular_part = M_PI / nchunks;

#pragma omp parallel for
    for(int chno = 0; chno < nchunks; chno++) {
        mt19937 rng;
        rng.seed(random_device()());
        uniform_int_distribution<int> dist122(lo, rad_hi(rng0));
        uniform_real_distribution<double> angle_gn(chno * angular_part, (chno + 1) * angular_part);

        int begin = chno * CHUNK_SIZE_RAND_REUSE;
        int end = min(n, (chno + 1) * CHUNK_SIZE_RAND_REUSE);

        for (int i = begin; i < end; i++) {
            auto radius = (int) dist122(rng);
            auto angle = (double) angle_gn(rng);
            A[i].x = ceil(abs(radius * cos(angle)));
            A[i].y = ceil(abs(radius * sin(angle)));
        }
    }
    return A;
}


Point* create_circle_distrib_point_1D_array(int n, double ratio){
    Point* A;
    A = (Point*) malloc(n * sizeof(Point));
    std::mt19937 rng;
    int chunksize = (int) (n / NUM_CHUNKS_DATAGEN) + 1;
    double r = sqrt(n * 1.) * DENSITY_FACTOR;
    double delta = ratio * r;
    double rmax = (ratio + 1) * r;
    double rmin = (1 - ratio) * r;
    double theta = M_PI / (2 * n);

#pragma omp parallel for
    for(int chunkno = 0; chunkno < NUM_CHUNKS_DATAGEN; chunkno++) {
        rng.seed(std::random_device()());
        std::uniform_real_distribution<> dist_delta(-delta, delta);
        for(int i = chunkno * chunksize; i < min(n, (chunkno +1) * chunksize); i++) {
            double dr = dist_delta(rng);
            double theta_i = i * theta;
            double x = abs((r + dr) * cos(theta_i));
            double y = abs((r + dr) * sin(theta_i));
            A[i].x = x;
            A[i].y = y;
        }
    }


    return A;
}

IDPair* create_hist_array(long n, int range) {
    if (range <= 0)
        return NULL;

    mt19937 rng;
    rng.seed(random_device()());
    uniform_int_distribution<int> kind(0, range);
    uniform_real_distribution<double> quantity(0., 10.0);

    IDPair* A;
    A = (IDPair*) malloc(n * sizeof(IDPair));

    for(long i = 0; i < n; i++) {
        A[i] = (IDPair){(int) kind(rng), (double) quantity(rng)};
    }
    return A;
}

/*
 * Creates a distribution of points with *numpoints* Pareto optimal points.
 * The Pareto optimal points define steps and the rest of the *n* points
 * are under these steps.
 */
Point* create_stair_distrib_point_1D_array(int n, double ratio) {
    if (0 >= ratio || ratio >= 1)
        return NULL;

    int numpoints = max((int) floor(ratio * n), 1);
    double ymax = sqrt(n);
    double avg_step = ymax / numpoints;


    Point *A;
    A = (Point*) malloc(n * sizeof(Point));
    for(int i = 0; i < n; i++) {
        A[i] = (Point) {0.,0.};
    }

    std::mt19937 rng;
    rng.seed(std::random_device()());
    std::uniform_real_distribution<double> dist(0., avg_step * 2);

    double xmax = 0.;
    double x = 0.;
    double y = ymax;
//    Generate the 'steps'
    for(int i = 0; i < numpoints; i++) {
        A[i] = (Point){ x, max(y, 0.0) };
        x += abs(dist(rng));
        y -= abs(dist(rng));
        xmax = max(xmax, x);
    }

    std::uniform_real_distribution<double> distx(0., ymax-1);
    std::uniform_real_distribution<double> disty(0., xmax-1);
    if(n > numpoints) {
        int i = numpoints;
        while(i < n) {
            Point p = { distx(rng), disty(rng)};
            bool iso = false;
            for(int k = 0; k < numpoints; k++) {
                iso = iso || (p.x >= A[k].x && p.y >= A[k].y);
            }
            if(!iso) {
                A[i] = p;
                i ++;
            }
        }
    }

//    SHUFFLE
    std::uniform_int_distribution<std::mt19937::result_type> distn(0, n-1);
    int j;
    for (int i = 0; i < numpoints; i++) {
        j = (int) distn(rng);
        swap(A[i], A[j]);
    }

    return A;
}


