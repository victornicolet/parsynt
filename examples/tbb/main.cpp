//
// Created by nicolet on 09/11/16.
//
#include <iostream>
#include "Stopwatch.h"
#include "Examples.h"
#include "ExampleUnit.h"

using namespace std;

int main(int argc, const char *argv[])
{
    //tbb::task_scheduler_init init(3);
    if (argc < 2)
    {
        std::cout << "no array size specified\n";
        exit(1);
    }

    int size = atoi(argv[1]);
    int size_mega = 1e+10;
    ExampleSumFoo e1(size_mega);
    e1.init();
    e1.print_result(cerr);


    return 0;
}