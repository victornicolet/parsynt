//
// Created by nicolet on 09/11/16.
//

#ifndef TBB_TESTS_EXAMPLEUNIT_H
#define TBB_TESTS_EXAMPLEUNIT_H

#include "Stopwatch.h"
#include <tbb/tbb.h>
#include <cmath>
#include <iostream>

using namespace tbb;
using namespace std;

template<class R>
class ExampleUnit {
    static string name;
public:
    virtual void init() = 0;
    virtual R parallel_apply() const = 0;
    virtual R seq_apply() const = 0;
};

#endif //TBB_TESTS_EXAMPLEUNIT_H
