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

class ExampleSum : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleSum(string name, size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int * _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleLength : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleLength(string name, size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleMax : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMax(string name,size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};


class ExampleMin : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMin(string name,size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;} ;
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleCountingOnes : public ExampleUnit<int, bool> {
    size_t n;
    bool *a = nullptr;
public:
    ExampleCountingOnes(string name,size_t n) : ExampleUnit<int, bool>(name), n(n) {}
    void init(bool* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleMpsPos : public ExampleUnit<size_t,int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMpsPos(string name,size_t n) : ExampleUnit<size_t, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    size_t parallel_apply() const;
    size_t seq_apply() const;
};

class ExampleMtsPos : public ExampleUnit<size_t, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMtsPos(string name,size_t n) : ExampleUnit<size_t, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    size_t parallel_apply() const;
    size_t seq_apply() const;
};

class ExampleMts : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMts(string name,size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleMps : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMps(string name,size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};


class ExampleMss : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMss(string name,size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleSecondMin : public ExampleUnit<int, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleSecondMin(string name,size_t n) : ExampleUnit<int, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleFirstOne : public ExampleUnit<size_t, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleFirstOne(string name,size_t n) : ExampleUnit<size_t, int>(name), n(n) {}
    void init(int* _a) override {a = _a;};
    size_t parallel_apply() const;
    size_t seq_apply() const;
};

class ExampleMaxLengthBlock : public ExampleUnit<int, bool> {
    size_t n;
    bool *a = nullptr;
public:
    ExampleMaxLengthBlock(string name,size_t n) : ExampleUnit<int, bool>(name), n(n) {}
    void init(bool *_a) override {a = _a;};
    int parallel_apply() const;
    int seq_apply() const;
};


/* Boolean return examples */

class ExampleIsSorted : public ExampleUnit<bool, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleIsSorted(string name,size_t n) : ExampleUnit<bool, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
};


class ExampleLineOfSight : public ExampleUnit<bool, int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleLineOfSight(string name,size_t n) : ExampleUnit<bool, int>(name), n(n) {}
    void init(int *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
};

class ExampleBalancedParenthesis : public ExampleUnit<bool, bool> {
    size_t n;
    bool *a = nullptr;
public:
    ExampleBalancedParenthesis(string name,size_t n) : ExampleUnit<bool, bool>(name), n(n) {}
    void init(bool *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
};

class ExampleSeen01 : public ExampleUnit<bool, bool> {
    size_t n;
    bool *a = nullptr;
public:
    ExampleSeen01(string name,size_t n) : ExampleUnit<bool, bool>(name), n(n) {}
    void init(bool *_a) override {a = _a;};
    bool parallel_apply() const;
    bool seq_apply() const;
};

#endif //TBB_TESTS_EXAMPLES_H
