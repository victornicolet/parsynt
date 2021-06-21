//
// Created by victorn on 22/10/18.
//

#ifndef NESTEDLOOPSEXPERIMENTS_DATAGEN_H
#define NESTEDLOOPSEXPERIMENTS_DATAGEN_H

#define CHUNK_SIZE_RAND_REUSE 100

struct Point {
    double x;
    double y;

    Point(double _x, double _y): x(_x), y(_y) {};

    bool operator==(const Point& a) const
    {
        return (x == a.x && y == a.y);
    }
};

struct IDPair {
    int kind;
    double quant;

    IDPair(int _x, double _y): kind(_x), quant(_y) {};

    bool operator==(const IDPair& x) const
    {
        return (kind == x.kind && quant == x.quant);
    }
};

void print_result_line(const std::string &experiment_name,
        const std::string &method,
        int num_threads, int n, int r,
        double ref_time, double exp_time);
int* create_rand_int_1D_array(long n);
int* create_randswapsort_int_1D_array(long n, long swaps);
float* create_randclo_int_1D_array(long n, long swaps);
int* create_randblocks_int_1D_array(long n, int avg_blocksize);
int** create_rand_int_2D_matrix(long num_cols, long num_rows);
int* create_rand_enum_1D_array(long n, int lo, int hi);
int*** create_rand_int_3D_matrix(long l, long m, long n);
bool** create_rand_bool_2D_matrix(long m, long n);
bool* create_rand_bool_1D_array(long n);
bool* create_randblocks_bool_1D_array(long n, int avg_blocksize);
Point* create_rand_point_1D_array(long n);
IDPair* create_hist_array(long n, int range);
Point* create_circle_distrib_point_1D_array(int n, double ratio);
Point* create_rand_segment_1D_array(long n, int max_value);
Point* create_segment_1D_array_cinter(int n, int max_value, int num_inters);
Point* create_rand_point_1D_array_circular(int n, int lo, int hi);
Point* create_stair_distrib_point_1D_array(int n, double ratio);
#endif //NESTEDLOOPSEXPERIMENTS_DATAGEN_H
