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


/** All the examples implemented here. */


std::list<string> examples_int_to_int = {"sum", "max", "min", "mi2", "mps", "mts", "mss"};
std::list<string> examples_bool_to_int= {"lbk", "col"};
std::list<string> examples_int_to_position = {"pop", "pot", "fs1", "len"};
std::list<string> examples_int_to_bool = {"los","sor"};
std::list<string> examples_bool_to_bool= {"bal", "s01"};
std::list<string> examples_custom = {"ins"};

bool mem (std::list<string> li, string el) {
    for (auto i = li.begin(), toofar = li.end(); i != toofar; ++i)
        if (*i == el)
            return true;
    return false;
}

template <class R, class I>
class Example {
public:
    ExampleUnit<R,I>* ex;
    Example(ExampleUnit<R,I>* _ex)  {
        if(ex) {
            ex = _ex;
        } else {
            cout << "Ooops... Example not valid." << endl;
            ex = NULL;
        }
    }

    void run(I* input, int num_runs) {
        (*ex).init(input);
        for(int i = 0; i < num_runs; i++)
            (*ex).parallel_apply();
    }
};

ExampleUnit<int, int>* ex_ii (string example_name, a_size pb_size) {
    if (example_name == "max") {
        return new ExampleMax("max", pb_size);
    } else if (example_name == "min") {
        return new ExampleMin("min", pb_size);
    } else if (example_name == "sum") {
        return new ExampleSum("sum", pb_size);
    } else if (example_name == "mi2") {
        return new ExampleSecondMin("mi2", pb_size);
    } else if (example_name == "mts") {
        return new ExampleMts("mts", pb_size);
    } else if (example_name == "mps") {
        return new ExampleMps("mps", pb_size);
    } else if (example_name == "mss") {
        return (new ExampleMss("mss", pb_size));
    } else {
        return NULL;
    }
}

ExampleUnit<int, bool>* ex_bi (string example_name, a_size pb_size) {
    if (example_name == "lbk") {
        return (new ExampleMaxLengthBlock("lbk", pb_size));
    } else if (example_name == "co1") {
        return (new ExampleCountingOnes("co1", pb_size));
    } else {
        return NULL;
    }
}

ExampleUnit<a_size, int>* ex_pi (string example_name, a_size pb_size) {
    if (example_name == "pop") {
        return (new ExampleMpsPos("pop", pb_size));
    } else if (example_name == "pot") {
        return (new ExampleMtsPos("pot", pb_size));
    } else if (example_name == "fs1") {
        return (new ExampleFirstOne("fs1", pb_size));
    } else if (example_name == "len") {
        return (new ExampleLength("len", pb_size));
    } else {
        return NULL;
    }
}

ExampleUnit<bool, int>* ex_ib (string example_name, a_size pb_size) {
    if (example_name == "los") {
        return (new ExampleLineOfSight("los", pb_size));
    } else if (example_name == "sor") {
        return (new ExampleIsSorted("sor", pb_size));
    } else {
        return NULL;
    }
}

ExampleUnit<bool, bool>* ex_bb (string example_name, a_size pb_size) {
    if (example_name == "bal") {
        return (new ExampleBalancedParenthesis("bal", pb_size));
    } else if (example_name == "s01") {
        return (new ExampleSeen01("s01", pb_size));
    }
}

ExampleInsertionSort* ex_special(string example_name, a_size pb_size) {
    if(example_name == "ins") {
        return (new ExampleInsertionSort("s01", pb_size));
    } else {
        return NULL;
    }
};

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

void do_only_one_example(int exp_size, int exp_num_core, string example_name) {
    /** Experiments :
            * num_cores from 0 to 64
            * size from 1e6 to 1e10 */
    a_size pb_size = 1L << exp_size;
    cout << "Example : " << example_name << endl;

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

    if (mem(examples_int_to_int, example_name)) {
        Example<int, int>(ex_ii(example_name, pb_size)).run(a_int, NUM_EXP_PER_CASE);
    } else if (mem(examples_bool_to_int, example_name)) {
        Example<int, bool>(ex_bi(example_name, pb_size)).run(a_bool, NUM_EXP_PER_CASE);
    } else if (mem(examples_int_to_bool, example_name)) {
        Example<bool, int>(ex_ib(example_name, pb_size)).run(a_int, NUM_EXP_PER_CASE);
    } else if (mem(examples_bool_to_bool, example_name)) {
        Example<bool, bool>(ex_bb(example_name, pb_size)).run(a_bool, NUM_EXP_PER_CASE);
    } else if (mem(examples_int_to_position, example_name)) {
        Example<a_size, int>(ex_pi(example_name, pb_size)).run(a_int, NUM_EXP_PER_CASE);
    } else {
        cout << "You 're sure you typed a correct example ?" << endl;
    }
    delete a_bool;
    delete a_int;
}


void do_special(int exp_size, int exp_num_core) {
    a_size pb_size = 1L << exp_size;

    cout << "Initialization for problem size " << pb_size << " ... " << endl;
    /* Allocate array of integers and array of booleans */
    int *a_1 = new int[pb_size];

    cout << "Arrays allocated" << endl;
    for(a_size ix = 0; ix < pb_size; ix++){
        a_1[ix] = rand() % 2000 - 1000;
    }
    cout << "Initialization succeeded." << endl;
    ofstream experiments;
    experiments.open("experiments.csv", fstream::app);

    cout << "Experiments for " << pb_size << " and " << exp_num_core << " cores." << endl;

    static tbb::task_scheduler_init
            init(tbb::task_scheduler_init::deferred);

    if(exp_num_core > 0)
        init.initialize(exp_num_core, UT_THREAD_DEFAULT_STACK_SIZE);

//    ExampleHamming ham("ham", pb_size);
//    ExampleMatchAB anbn("abn", pb_size, 500, 300);
    ExampleInsertionSort insertionSort("ins", pb_size);

    for(int i = 0; i < NUM_EXP_PER_CASE; i++) {
//        ham.init(a_1, a_2);
//        ham.serialize(exp_num_core, pb_size, experiments);

//        anbn.init(a_1);
//        anbn.serialize(exp_num_core, pb_size, experiments);
        insertionSort.init(a_1);
        insertionSort.serialize(exp_num_core, pb_size, experiments);
    }

    delete a_1;

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
    string example_name = "sum";
    bool launch_experiments = true;
    bool special_experiment = false;
    bool name_provided = false;
    while ((opt = getopt(argc, argv, "n:s:e:x")) != -1) {
        switch (opt) {
            case 'n':
                num_cores = atoi(optarg);
                break;
            case 's':
                exp_sizes = atoi(optarg);
                break;
            case 'x':
                launch_experiments = false;
                special_experiment = true;
                break;
            case 'e':
                name_provided = true;
                launch_experiments = false;
                example_name = optarg;
                break;
            default: /* '?' */
                cerr << "Usage: " << argv[0] << "[-e example_name] [-n ncores] [-s power of two size]\n";
                exit(EXIT_FAILURE);
        }
    }

    if(name_provided) {
        do_only_one_example(exp_sizes, num_cores, example_name);
    } else {

        if (launch_experiments && !special_experiment) {
            do_experiment(exp_sizes, num_cores);
        } else if (special_experiment) {
            do_special(exp_sizes, num_cores);
        } else {
            cerr << "Usage: " << argv[0] << "[-x example_name] [-n ncores] [-e power of two size]\n";
        }
    }

    return 0;
}