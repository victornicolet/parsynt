//
// Created by nicolet on 09/11/16.
//
#include <tbb/tbb.h>
#include "ExampleUnit.h"

#ifndef TBB_TESTS_EXAMPLES_H
#define TBB_TESTS_EXAMPLES_H

using namespace std;

class ExampleSumFoo : public ExampleUnit<int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleSumFoo(string name, size_t n) : ExampleUnit<int>(name), n(n) {}
    ~ExampleSumFoo();
    void init() override;
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleLength : public ExampleUnit<int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleLength(string name, size_t n) : ExampleUnit<int>(name), n(n) {}
    ~ExampleLength();
    void init() override;
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleMax : public ExampleUnit<int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMax(string name,size_t n) : ExampleUnit<int>(name), n(n) {}
    ~ExampleMax();
    void init() override;
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleMin : public ExampleUnit<int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMin(string name,size_t n) : ExampleUnit<int>(name), n(n) {}
    ~ExampleMin();
    void init() override;
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleCountingOnes : public ExampleUnit<int> {
    size_t n;
    bool *a = nullptr;
public:
    ExampleCountingOnes(string name,size_t n) : ExampleUnit<int>(name), n(n) {}
    ~ExampleCountingOnes();
    void init() override;
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleMpsPos : public ExampleUnit<int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleMpsPos(string name,size_t n) : ExampleUnit<int>(name), n(n) {}
    ~ExampleMpsPos();
    void init() override;
    int parallel_apply() const;
    int seq_apply() const;
};

class ExampleSecondMin : public ExampleUnit<int> {
    size_t n;
    int *a = nullptr;
public:
    ExampleSecondMin(string name,size_t n) : ExampleUnit<int>(name), n(n) {}
    ~ExampleSecondMin();
    void init() override;
    int parallel_apply() const;
    int seq_apply() const;
};


/* Boolean return examples */

class ExampleIsSorted : public ExampleUnit<bool> {
    size_t n;
    int *a = nullptr;
public:
    ExampleIsSorted(string name,size_t n) : ExampleUnit<bool>(name), n(n) {}
    ~ExampleIsSorted();
    void init() override;
    bool parallel_apply() const;
    bool seq_apply() const;
};


class ExampleLineOfSight : public ExampleUnit<bool> {
    size_t n;
    int *a = nullptr;
public:
    ExampleLineOfSight(string name,size_t n) : ExampleUnit<bool>(name), n(n) {}
    ~ExampleLineOfSight();
    void init() override;
    bool parallel_apply() const;
    bool seq_apply() const;
};

#endif //TBB_TESTS_EXAMPLES_H
