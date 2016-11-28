//
// Created by nicolet on 09/11/16.
//
#define UT_THREAD_DEFAULT_STACK_SIZE (8U*1024U*1024U)
#define NUM_EXP_PER_CASE 20

#include <iostream>
#include <fstream>
#include <sstream>
#include <unistd.h>
#include "Examples/Examples.h"
#include "Examples/ExampleUnit.h"

using namespace std;

typedef ExampleUnit<int, bool>* IBEx;
typedef ExampleUnit<bool, int>* BIEx;
typedef ExampleUnit<bool, bool>* BBEx;
typedef ExampleUnit<int, int>* IIEx;
typedef ExampleUnit<a_size, int>* PIEx;

void do_experiment(int exp_size, int exp_num_core) {
    /** Experiments :
            * num_cores from 0 to 64
            * size from 1e6 to 1e10 */
    a_size pb_size = 1L << exp_size;

    ofstream experiments;
    experiments.open("experiments.csv", fstream::app);

    cout << "Initialization for problem size " << pb_size << " ... " << endl;
    /* Allocate array of integers and array of booleans */
    int *a_int = new int[pb_size];
    bool *a_bool = new bool[pb_size];

    cout << "Arrays allocated" << endl;
    for(a_size ix = 0; ix < pb_size; ix++){
        a_int[ix] = rand() % 2000 - 1000;
        a_bool[ix] = a_int[ix] > 0;
    }
    cout << "Initialization succeeded." << endl;

    cout << "Experiments for " << pb_size << " and " << exp_num_core << " cores." << endl;

    static tbb::task_scheduler_init
            init(tbb::task_scheduler_init::deferred);

    if(exp_num_core > 0)
        init.initialize(exp_num_core, UT_THREAD_DEFAULT_STACK_SIZE);



    for(int i = 0; i < NUM_EXP_PER_CASE; i++) {

        std::list<IIEx> li_ii_ex = {};
        std::list<IBEx> li_ib_ex = {};
        std::list<PIEx> li_pi_ex = {};
        std::list<BBEx> li_bb_ex = {};
        std::list<BIEx> li_bi_ex = {};

        li_ii_ex.push_back(new ExampleSum("sum", pb_size));
        li_ii_ex.push_back(new ExampleMax("max", pb_size));
        li_ii_ex.push_back(new ExampleMin("min", pb_size));
        li_ii_ex.push_back(new ExampleSecondMin("mi2", pb_size));
        li_ii_ex.push_back(new ExampleMps("mps", pb_size));
        li_ii_ex.push_back(new ExampleMts("mts", pb_size));
        li_ii_ex.push_back(new ExampleMss("mss", pb_size));


        li_ib_ex.push_back(new ExampleMaxLengthBlock("lbk", pb_size));
        li_ib_ex.push_back(new ExampleCountingOnes("co1", pb_size));

        li_pi_ex.push_back(new ExampleMpsPos("pop", pb_size));
        li_pi_ex.push_back(new ExampleMtsPos("pot", pb_size));
        li_pi_ex.push_back(new ExampleFirstOne("fs1", pb_size));
        li_pi_ex.push_back(new ExampleLength("len", pb_size));


        li_bi_ex.push_back(new ExampleLineOfSight("los", pb_size));
        li_bi_ex.push_back(new ExampleIsSorted("sor", pb_size));
        li_bb_ex.push_back(new ExampleBalancedParenthesis("bal", pb_size));
        li_bb_ex.push_back(new ExampleSeen01("s01", pb_size));

        /* Integer inputs */
        for (auto ex : li_ii_ex) {
            (*ex).init(a_int);
            (*ex).serialize(exp_num_core, pb_size, experiments);
        }
        for (auto ex : li_bi_ex) {
            (*ex).init(a_int);
            (*ex).serialize(exp_num_core, pb_size, experiments);
        }
        for (auto ex : li_pi_ex) {
            (*ex).init(a_int);
            (*ex).serialize(exp_num_core, pb_size, experiments);
        }


        /* Boolean inputs */
        for (auto ex : li_bb_ex) {
            (*ex).init(a_bool);
            (*ex).serialize(exp_num_core, pb_size, experiments);
        }
        for (auto ex : li_ib_ex) {
            (*ex).init(a_bool);
            (*ex).serialize(exp_num_core, pb_size, experiments);
        }

    }

    delete a_bool;
    delete a_int;

    experiments.close();
}


void do_special(int exp_size, int exp_num_core) {
    a_size pb_size = 1L << exp_size;

    cout << "Initialization for problem size " << pb_size << " ... " << endl;
    /* Allocate array of integers and array of booleans */
    int *a_1 = new int[pb_size];
    int *a_2 = new int[pb_size];

    cout << "Arrays allocated" << endl;
    for(a_size ix = 0; ix < pb_size; ix++){
        a_1[ix] = rand() % 2000 - 1000;
        a_2[ix] = rand() % 2000 - 1000;
    }
    cout << "Initialization succeeded." << endl;
    ofstream experiments;
    experiments.open("experiments.csv", fstream::app);

    cout << "Experiments for " << pb_size << " and " << exp_num_core << " cores." << endl;

    static tbb::task_scheduler_init
            init(tbb::task_scheduler_init::deferred);

    if(exp_num_core > 0)
        init.initialize(exp_num_core, UT_THREAD_DEFAULT_STACK_SIZE);

    ExampleHamming ham("ham", pb_size);
    ExampleMatchAB anbn("abn", pb_size, 500, 300);

    for(int i = 0; i < NUM_EXP_PER_CASE; i++) {
        ham.init(a_1, a_2);
        ham.serialize(exp_num_core, pb_size, experiments);

        anbn.init(a_1);
        anbn.serialize(exp_num_core, pb_size, experiments);
    }

    delete a_1;
    delete a_2;

    experiments.close();
}

void launch_exp_whyonefaster () {
    a_size exp_size = 1L << 31;
    int exp_num_core = 1;

    ofstream whyonefaster;
    whyonefaster.open("whyonefaster.csv", fstream::app);

    cout << "Initialization for problem size " << exp_size << " ... " << endl;
    /* Allocate array of integers and array of booleans */
    int *ar = new int[exp_size];

    cout << "Arrays allocated" << endl;
    for (a_size ix = 0; ix < exp_size; ix++) {
        ar[ix] = rand() % 2000 - 1000;
    }
    cout << "Initialization succeeded." << endl;

    cout << "Experiments for " << exp_size << " and " << exp_num_core << " cores." << endl;

    static tbb::task_scheduler_init
            init(tbb::task_scheduler_init::deferred);

    if (exp_num_core > 0)
        init.initialize(exp_num_core, UT_THREAD_DEFAULT_STACK_SIZE);

    ExampleLineOfSight los("los", exp_size);
    los.init(ar);
    for (int i = 0; i < 10; i++) {
        los.serialize(0, exp_size, whyonefaster);
        los.serialize(exp_num_core, exp_size, whyonefaster);
    }
    whyonefaster.close();
}

int main(int argc, char *argv[]) {
    int opt;
    int num_cores = 1;
    int exp_sizes = 1;
    bool launch_experiments = false;
    bool special_experiment = false;
    while ((opt = getopt(argc, argv, "n:e:s:x:")) != -1) {
        switch (opt) {
            case 'n':
                num_cores = atoi(optarg);
                break;
            case 'e':
                exp_sizes = atoi(optarg);
                launch_experiments = true;
                break;
            case 's':
                exp_sizes = atoi(optarg);
                special_experiment = true;
                break;
            case 'x':
                launch_exp_whyonefaster();
            default: /* '?' */
                cerr << "Usage: " << argv[0] << " [-n ncores] [-e power of two size]\n";
                exit(EXIT_FAILURE);
        }
    }


    if(launch_experiments) {
        do_experiment(exp_sizes, num_cores);
    } else if (special_experiment) {
        do_special(exp_sizes, num_cores);
    } else {
        cout << "WIP oprtions -n and -s, only -e -n working for now.";
    }

    return 0;
}