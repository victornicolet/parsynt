//
// Created by nicolet on 09/11/16.
//
#include "Stopwatch.h"
#include <tbb/tbb.h>
#include <cmath>
#include <iostream>

#ifndef TBB_TESTS_EXAMPLEUNIT_H
#define TBB_TESTS_EXAMPLEUNIT_H

using namespace tbb;
using namespace std;

template<class R>
class ExampleUnit {
public:
    string name;
    ExampleUnit(string _n) : name(_n) {}
    virtual void init() = 0;
    virtual R parallel_apply() const = 0;
    virtual R seq_apply() const = 0;
    void print_result(ostream& out) {
        StopWatch u;
        u.start();
        R result = parallel_apply();
        double elapsed = u.stop();
        out << "Example " << name << endl;
        out << "Parallel : " <<  result << " in time : " << elapsed << endl;
        StopWatch w;
        w.start();
        R seq_res = seq_apply();
        out << "Serial : " << seq_res << " in time: " << w.stop() << endl;
    };
};

#endif //TBB_TESTS_EXAMPLEUNIT_H
