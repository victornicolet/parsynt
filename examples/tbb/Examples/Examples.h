//
// Created by nicolet on 09/11/16.
//
#include <tbb/tbb.h>
#include "ExampleUnit.h"

#ifndef TBB_TESTS_EXAMPLES_H
#define TBB_TESTS_EXAMPLES_H


/*
 * Examples implemented :
 *
 * Examples returning an integer :
 * - Sum
 * - Length
 * - Min
 * - Second min element
 * - Max
 * - Second max element
 * - Mts
 * - Mss
 * - Mps with pos
 * - Mts with pos
 * - Counting blocks of ones
 * - Length of greatest block of trues
 * - Position of first one in block
 *
 * Examples returning a boolean :
 * - Line of sight
 * - Is Sorted
 * - Is balanced
 * - Seen true after false
 */

using namespace std;

typedef long a_size;

class ExampleSum : public ExampleUnit<int, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleSum(string name, a_size n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int * _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};

class ExampleLength : public ExampleUnit<a_size, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleLength(string name, a_size n) : ExampleUnit<a_size , int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    a_size parallel_apply() const;
    a_size seq_apply() const;
    a_size full_seq_apply() const;
};

class ExampleMax : public ExampleUnit<int, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleMax(string name,a_size n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};


class ExampleMin : public ExampleUnit<int, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleMin(string name,a_size n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;} ;
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};

class ExampleCountingOnes : public ExampleUnit<int, bool> {
    a_size n;
    bool *a = nullptr;
public:
    ExampleCountingOnes(string name,a_size n) : ExampleUnit<int, bool>(name), n(n) {}
    void init(bool* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};

class ExampleMpsPos : public ExampleUnit<a_size,int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleMpsPos(string name,a_size n) : ExampleUnit<a_size, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    a_size parallel_apply() const;
    a_size seq_apply() const;
    a_size full_seq_apply() const;
};

class ExampleMtsPos : public ExampleUnit<a_size, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleMtsPos(string name,a_size n) : ExampleUnit<a_size, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    a_size parallel_apply() const;
    a_size seq_apply() const;
    a_size full_seq_apply() const;
};

class ExampleMts : public ExampleUnit<int, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleMts(string name,a_size n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};

class ExampleMps : public ExampleUnit<int, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleMps(string name,a_size n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};


class ExampleMss : public ExampleUnit<int, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleMss(string name,a_size n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};

class ExampleSecondMin : public ExampleUnit<int, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleSecondMin(string name,a_size n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};

class ExampleFirstOne : public ExampleUnit<a_size, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleFirstOne(string name,a_size n) : ExampleUnit<a_size, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    a_size parallel_apply() const;
    a_size seq_apply() const;
    a_size full_seq_apply() const;
};

class ExampleMaxLengthBlock : public ExampleUnit<int, bool> {
    a_size n;
    bool *a = nullptr;
public:
    ExampleMaxLengthBlock(string name,a_size n) : ExampleUnit<int, bool>(name), n(n) {}
    void init(bool *_a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
    int full_seq_apply() const;
};


/* Boolean return examples */

class ExampleIsSorted : public ExampleUnit<bool, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleIsSorted(string name,a_size n) : ExampleUnit<bool, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
    bool full_seq_apply() const;
};


class ExampleLineOfSight : public ExampleUnit<bool, int> {
    a_size n;
    int *a = nullptr;
public:
    ExampleLineOfSight(string name,a_size n) : ExampleUnit<bool, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
    bool full_seq_apply() const;
};

class ExampleBalancedParenthesis : public ExampleUnit<bool, bool> {
    a_size n;
    bool *a = nullptr;
public:
    ExampleBalancedParenthesis(string name,a_size n) : ExampleUnit<bool, bool>(name), n(n) {}
    void init(bool *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
    bool full_seq_apply() const;
};

class ExampleSeen01 : public ExampleUnit<bool, bool> {
    a_size n;
    bool *a = nullptr;
public:
    ExampleSeen01(string name,a_size n) : ExampleUnit<bool, bool>(name), n(n) {}
    void init(bool *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
    bool full_seq_apply() const;
};


/* The only example with two inputs */
class ExampleHamming  {
    a_size n;
    int *a = nullptr;
    int *b = nullptr;
public:
    string name;
    ExampleHamming(string name, a_size n) : name(name), n(n) {}
    void init(int *_, int *_b) { a = _a; b = _b;};
    int parallel_apply ();
    int seq_apply ();
    int full_seq_apply() {return seq_apply();}


    void serialize(int num_cores, a_size pb_size, ofstream& of) {
        if (num_cores == -1) {
            StopWatch u;
            u.start();
            int seq_res = full_seq_apply();
            double elapsed = u.stop();
            of << name << "," << num_cores << "," << pb_size <<"," << elapsed << "\n";
        }
        else if (num_cores == 0) {
            StopWatch u;
            u.start();
            int seq_res = seq_apply();
            double elapsed = u.stop();
            of << name << "," << num_cores << "," << pb_size <<"," << elapsed << "\n";
        } else {
            StopWatch u;
            u.start();
            int par_res = parallel_apply();
            double par_elapsed = u.stop();
            of << name << "," << num_cores << "," << pb_size <<"," << par_elapsed << "\n";
        }
    }
};

#endif //TBB_TESTS_EXAMPLES_H
