//
// Created by nicolet on 09/11/16.
//
#define UT_THREAD_DEFAULT_STACK_SIZE (8U*1024U*1024U)


#include <iostream>
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

    while ((opt = getopt(argc, argv, "s:n:")) != -1) {
        switch (opt) {

            case 's':
                problem_size = atol(optarg);
                break;
            case 'n':
                num_cores = atoi(optarg);
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

    std::list<IntEx*> li = {};

    li.push_back(new ExampleSum("sum", problem_size));
    li.push_back(new ExampleLength("length", problem_size));
    li.push_back(new ExampleMax("max", problem_size));
    li.push_back(new ExampleMin("min", problem_size));
    li.push_back(new ExampleCountingOnes("counting blocks of ones (true)", problem_size));
    li.push_back(new ExampleMps("maximum prefix sum", problem_size));
    li.push_back(new ExampleMts("maximum terminal sum", problem_size));
    li.push_back(new ExampleMss("maximum segment sum", problem_size));
    li.push_back(new ExampleMpsPos("position of max prefix sum", problem_size));
    li.push_back(new ExampleMtsPos("position of max terminal sum", problem_size));
    li.push_back(new ExampleSecondMin("second min element", problem_size));
    li.push_back(new ExampleFirstOne("position of first one in sequence", problem_size));
    li.push_back(new ExampleMaxLengthBlock("Length of biggest block of true", problem_size));

    for(auto ex : li) {
        (*ex).init();
        (*ex).print_result(cout);
        delete ex;
    }

    li.empty();

    std::list<BoolEx*> li2 = {};

    li2.push_back(new ExampleLineOfSight("Line of sight", problem_size));
    li2.push_back(new ExampleIsSorted("Is sorted", problem_size));
    li2.push_back(new ExampleBalancedParenthesis("Balanced parenthesis", problem_size));

    for(auto ex : li2) {
        (*ex).init();
        (*ex).print_result(cout);
        delete ex;
    }

    li2.empty();

    return 0;
}