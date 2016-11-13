//
// Created by nicolet on 09/11/16.
//
#include "Stopwatch.h"
#include <tbb/tbb.h>
#include <cmath>
#include <iostream>
#include <fstream>


#ifndef TBB_TESTS_EXAMPLEUNIT_H
#define TBB_TESTS_EXAMPLEUNIT_H

using namespace tbb;
using namespace std;
typedef long a_size;

template<class R, class I>
class ExampleUnit {
public:
    string name;
    ExampleUnit(string _n) : name(_n) {}
    virtual void init(I*) = 0;
    virtual R parallel_apply() const = 0;
    virtual R seq_apply() const = 0;
    virtual R full_seq_apply() const = 0;


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

    /* File ofstream must be opened before calling serialize.
     * If the number of cores provided  is 0, use sequential time. */

    void serialize(int num_cores, a_size pb_size, ofstream& of) {
        if (num_cores == -1) {
            StopWatch u;
            u.start();
            R seq_res = full_seq_apply();
            double elapsed = u.stop();
            of << name << "," << num_cores << "," << pb_size <<"," << elapsed << "\n";
        }
        else if (num_cores == 0) {
            StopWatch u;
            u.start();
            R seq_res = seq_apply();
            double elapsed = u.stop();
            of << name << "," << num_cores << "," << pb_size <<"," << elapsed << "\n";
        } else {
            StopWatch u;
            u.start();
            R par_res = parallel_apply();
            double par_elapsed = u.stop();
            of << name << "," << num_cores << "," << pb_size <<"," << par_elapsed << "\n";
        }
    }
};

#endif //TBB_TESTS_EXAMPLEUNIT_H
