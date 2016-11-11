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
typedef ExampleUnit<size_t, int>* PIEx;

void do_experiment(int exp_sizes) {
    /** Experiments :
            * num_cores from 0 to 64
            * size from 1e6 to 1e10 */
    list<int> exp_num_core_li = {0, 1, 2, 4, 6, 8, 16, 32, 64};
    list<size_t> pb_size_li = {1<< exp_sizes, (1 << exp_sizes + 1)};

    ofstream experiments;
    experiments.open("experiments.csv", fstream::app);

    for(size_t pb_size : pb_size_li) {
        cout << "Initialization for problem size " << pb_size << " ... " << endl;
        /* Allocate array of integers and array of booleans */
        int *a_int = new int[pb_size];
        bool *a_bool = new bool[pb_size];


        for(size_t ix = 0; ix < pb_size; ix++){
            a_int[ix] = rand() % 100 - 50;
            a_bool[ix] = a_int[ix] > 0;
        }
        cout << "Initialization succeeded." << endl;

        for(int exp_num_core : exp_num_core_li) {

            cout << "Experiments for " << pb_size << " and " << exp_num_core << " cores." << endl;

            for(int i = 0; i < NUM_EXP_PER_CASE; i++) {

                std::list<IIEx> li_ii_ex = {};
                std::list<IBEx> li_ib_ex = {};
                std::list<PIEx> li_pi_ex = {};
                std::list<BBEx> li_bb_ex = {};
                std::list<BIEx> li_bi_ex = {};

                li_ii_ex.push_back(new ExampleSum("sum", pb_size));
                li_ii_ex.push_back(new ExampleLength("len", pb_size));
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
        }

        delete a_bool;
        delete a_int;
    }

    experiments.close();

    ifstream exps;
    exps.open("experiments.csv");
    cout << "Printing the results of the experiments." << endl;
    string cur_inpt;
    while(getline(exps, cur_inpt)) {
        cout << cur_inpt <<endl;
    }
    exps.close();
}

int main(int argc, char *argv[]) {
    int opt;
    long problem_size = 1000000;
    int num_cores = 1;
    int exp_sizes = 1;
    bool launch_experiments = false;
    while ((opt = getopt(argc, argv, "s:n:e:")) != -1) {
        switch (opt) {

            case 's':
                problem_size = atol(optarg);
                break;
            case 'n':
                num_cores = atoi(optarg);
                break;
            case 'e':
                exp_sizes = atoi(optarg);
                launch_experiments = true;
                break;
            default: /* '?' */
                cerr << "Usage: " << argv[0] << " [-s nsecs] [-n ncores] [-e power of two size]\n";
                exit(EXIT_FAILURE);
        }
    }

    cout << "Number of cores : " << num_cores << "\nProblem size : " << problem_size << endl;

    // If a number of cores is specified and greate than 1,
    // then set then number of cores used by TBB.
    if (num_cores > 1) {
        static tbb::task_scheduler_init
                init(tbb::task_scheduler_init::deferred);

        init.initialize(num_cores, UT_THREAD_DEFAULT_STACK_SIZE);
    }


    if(launch_experiments) {
        do_experiment(exp_sizes);
    } else {
        cout << "WIP oprtions -n and -s, only -e working for now.";
    }

    return 0;
}