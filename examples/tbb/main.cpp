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

typedef ExampleUnit<int> IntEx;
typedef ExampleUnit<bool> BoolEx;

int main(int argc, char *argv[]) {
    int opt;
    long problem_size = 1000000;
    int num_cores = 1;
    bool launch_experiments = false;
    while ((opt = getopt(argc, argv, "s:n:e")) != -1) {
        switch (opt) {

            case 's':
                problem_size = atol(optarg);
                break;
            case 'n':
                num_cores = atoi(optarg);
                break;
            case 'e':
                launch_experiments = true;
                break;
            default: /* '?' */
                cerr << "Usage: " << argv[0] << " [-s nsecs] [-n ncores]\n";
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
        /** Experiments :
         * num_cores from 0 to 64
         * size from 1e6 to 1e10 */
        list<int> exp_num_core_li = {1, 2, 4, 6, 8, 16, 32, 64};
        list<int> pb_size_li = {1<< 20, 1 << 22, 1 << 24, 1 << 26, 1 << 28, 1 << 30, 1 << 32 - 1};

        ofstream experiments;
        experiments.open("experiments.csv", fstream::app);

        for(int exp_num_core : exp_num_core_li) {

            for(int pb_size : pb_size_li) {

                cout << "Experiments for " << pb_size << " and " << exp_num_core << " cores." << endl;

                for(int i = 0; i < NUM_EXP_PER_CASE; i++) {
                    std::list<IntEx *> li_e = {};

                    li_e.push_back(new ExampleSum("sum", pb_size));
                    li_e.push_back(new ExampleLength("len", pb_size));
                    li_e.push_back(new ExampleMax("max", pb_size));
                    li_e.push_back(new ExampleMin("min", pb_size));
                    li_e.push_back(new ExampleCountingOnes("co1", pb_size));
                    li_e.push_back(new ExampleMps("mps", pb_size));
                    li_e.push_back(new ExampleMts("mts", pb_size));
                    li_e.push_back(new ExampleMss("mss", pb_size));
                    li_e.push_back(new ExampleMpsPos("pop", pb_size));
                    li_e.push_back(new ExampleMtsPos("pot", pb_size));
                    li_e.push_back(new ExampleSecondMin("mi2", pb_size));
                    li_e.push_back(new ExampleFirstOne("fs1", pb_size));
                    li_e.push_back(new ExampleMaxLengthBlock("lbk", pb_size));

                    for (auto ex : li_e) {
                        (*ex).init();
                        (*ex).serialize(exp_num_core, pb_size, experiments);
                        delete ex;
                    }

                    std::list<BoolEx *> li_e2 = {};

                    li_e2.push_back(new ExampleLineOfSight("los", pb_size));
                    li_e2.push_back(new ExampleIsSorted("sor", pb_size));
                    li_e2.push_back(new ExampleBalancedParenthesis("bal", pb_size));
                    li_e2.push_back(new ExampleSeen01("s01", pb_size));

                    for (auto ex : li_e2) {
                        (*ex).init();
                        (*ex).serialize(exp_num_core, pb_size, experiments);
                        delete ex;
                    }
                }
            }
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
    } else {
        std::list<IntEx*> li = {};

        li.push_back(new ExampleSum("sum", problem_size));
        li.push_back(new ExampleLength("len", problem_size));
        li.push_back(new ExampleMax("max", problem_size));
        li.push_back(new ExampleMin("min", problem_size));
        li.push_back(new ExampleCountingOnes("co1", problem_size));
        li.push_back(new ExampleMps("mps", problem_size));
        li.push_back(new ExampleMts("mts", problem_size));
        li.push_back(new ExampleMss("mss", problem_size));
        li.push_back(new ExampleMpsPos("pop", problem_size));
        li.push_back(new ExampleMtsPos("pot", problem_size));
        li.push_back(new ExampleSecondMin("mi2", problem_size));
        li.push_back(new ExampleFirstOne("fs1", problem_size));
        li.push_back(new ExampleMaxLengthBlock("lbk", problem_size));


        for(auto ex : li) {
            (*ex).init();
            (*ex).print_result(cout);
            delete ex;
        }

        std::list<BoolEx*> li2 = {};

        li2.push_back(new ExampleLineOfSight("los", problem_size));
        li2.push_back(new ExampleIsSorted("sor", problem_size));
        li2.push_back(new ExampleBalancedParenthesis("bal", problem_size));
        li2.push_back(new ExampleSeen01("s01", problem_size));

        for(auto ex : li2) {
            (*ex).init();
            (*ex).print_result(cout);
            delete ex;
        }
    }

    return 0;
}