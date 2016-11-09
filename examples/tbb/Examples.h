//
// Created by nicolet on 09/11/16.
//

#ifndef TBB_TESTS_EXAMPLES_H
#define TBB_TESTS_EXAMPLES_H

#include <tbb/tbb.h>
#include "ExampleUnit.h"

using namespace std;

class ExampleSumFoo : public ExampleUnit<double> {
    size_t n;
    int *a = nullptr;
    static string name;
public:
    ExampleSumFoo(size_t n) : n(n) {}
    ~ExampleSumFoo();
    void init() override;
    double parallel_apply() const;
    double seq_apply() const;
    void print_result(ostream& out) const;
};

#endif //TBB_TESTS_EXAMPLES_H
