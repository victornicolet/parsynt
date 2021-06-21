
# Phased Synthesis of Divide and Conquer Programs

This guide outlines how the results presented in the paper Phased Synthesis of Divide and Conquer 
Programs can be reproduced.

## Claims of the paper
The two main claims made in our paper, can be briefly summarized as follows: (i) the tool Parsynt
 can synthesize non-trivial divide-and-conquer algorithms from
iterative algorithms in reasonable time (paragraph *Performance of Parsynt* in Section 8). (ii) the
solutions synthesized provide a performance advantage over the input implementation. This advantage
resides either in the fact that the divide-and-conquer algorithm has lower asymptotic complexity,
or because it can be efficiently parallelized (paragraph *Quality of the Synthesized Code* in Section 8).

(i) All the scripts in this folder that will allow the reviewer to reproduce the results presented
 are included here. 
In order to test that Parsynt is in working order, the tool can be run on one of the input benchmarks 
provided. For example, running the following command should print the solution for the parallel largest 
peak algorithm in a few seconds:
```./Parsynt inputs/table7a/lmo.minic```
Harder to solve examples are included in the `inputs/table1` folder. One of the simpler examples is
sorting. The following command should produce an answer in less than 30 seconds:
```./Parsynt inputs/table1/sorting.minic -k 0 -m 2 -c 2```
While performance may vary significantly across platforms, our goal is to show that Parsynt can
synthesize non-trivial solutions in reasonable time. We expect the synthesis of each benchmark
included to take less than 10 min.

(ii) Our tool produces divide-and-conquer algorithms that can be implemented in any language. We show
in Figures 4, 7b, 7c of the paper in Figure 12 of the Appendix that these solutions have varied
performance advantage over the inputs implementations. We go into more detail later on the scripts
included to generate the graphs in the figures, both from existing data and generated data.
In order to test that everything is in order, the reviewer can run the script `./all.sh` from the
root folder. The script should take about 10 min to complete. If successful, there should be 18
PDF files in the folder. 9 files should have the suffix *_bis.pdf* corresponding to graphs from
generated experimental results, and the other files corresponding to graphs from our experimental
results.

---------------------------
# Step-by-step instructions

We have provided scripts that will allow the reviewer to reproduce the results presented in the
paper. At any point during the evaluation, the reviewer can run `./clean_data.sh` from the root
folder to remove any generated experimental data.

## (i) Evaluating the Performance of Parsynt

The scripts to reproduce the results presented in Table 1 and Table 7a of the paper are included in
the root folder and called `table1.py` and `table7a.py` respectively.

### Running the experiments
Running `./scripts/table7a.py` should take no more than 10 minutes, and the output is stored in
`table7a.txt`. Running the script produces first a `.csv` file containing all the measured running
times for the different benchmarks in `inputs/table7a/timings.csv`. The script then builds the
summary results in the text file. You can provide an additional integer argument to the script to
run the tool on the benchmarks more than once ('./table7a n` to repeat n times), and `table7a` will
contain an average of the synthesis time across all runs.

Running `./scripts/table1.py` should take around 30 minutes. The intermediary experimental results are written
in `inputs/table1/timings.csv` and summarized in `table1.txt`. Given the limited amount of time for
the review, the scripts only runs each benchmarks once, but as for the previous set, reviewers can
decide to build a more convincing data set.


### Interpreting the results
The claim we make in the paper is that the tool Parsynt succeeds in synthesizing divide-and-conquer
programs from iterative implementations in reasonable time. We do not expect the reviewer to obtain
the same results as the ones presented in the paper, but we expect that total synthesis time for any
benchmark should not exceed 10 min.

The difference in timing may vary non-uniformly across benchmarks, as the tool splits the problem
into sub-problems differently in the various synthesis phases. We included experimental results for
Table 1 and Table 7a for two different platforms in the folders `inputs/table1` and
`inputs/table7a`. Note that for the results reported in the paper, we had access to a machine with
16 cores and 32 GB of RAM. In `laptop_results.txt` we report the results obtained by running the
tests on a laptop in reporting the results obtained on a laptop with a 6-core Intel Core i7-8750H
CPU @ 2.20GHz and 16GB RAM running Ubuntu 20.04. The tool is able to take advantage of all the cores
in the more complex benchmarks of the paper, in particular for the join synthesis where some
components are synthesized in parallel. The reviewer should notice that the performance of
Parsynt on the benchmarks of Table 1 has been significantly improved.

### Running the tool on single benchmarks

In order to understand the non-triviality of the task, the reviewer may want to run the tool on some
of the provided benchmarks and analyze the divide-and-conquer algorithms synthesized. Our tool
focuses on translating algorithms to other algorithms, and as such, the output of the tool is not an
implementation in a specific language but a description of the divide-and-conquer algorithm, in one
of the following forms.

#### Benchmarks of Table 1
The benchmarks in Table 1 have implementations that are partitioning divide-and-conquer
implementations. For these benchmarks, an output lists the following components:
- A *single-pass function* that is to be used to compute partial results on the partitions resulting
  from the divide. The single-pass function follows the model described in Appendix C.2, and the
  tool prints its full definition.
- A divide function specifies how the divide-and-conquer algorithm partitions the input list into
two or more output lists. A partition divide typically first finds one or more pivots, and then
partition the input list with a predicate using this pivot.
- A join function, which joins the outputs of the function applied to each of the partitions. The
  join function has two or more arguments that represent the partial results.

There are two ways to run the tools on the benchmarks. One way is to specify a budget, as it is done
in the script `./scripts/table1.py`. The reviewer can refer to the script to match the benchmarks referred in
the paper with the corresponding input file. For example, one can obtain the solution with lifting
described in Section 2 for the Pareto examples by running the following command:
```
./Parsynt inputs/table1/pareto.minic -k 0 -m 2 -c 2
```
The solution synthesized may slightly differ from the one presented in the paper, but should
correspond to the same principle: the divide function splits the space along some criteria, and the
join is a linear-time function that checks the optimality of the points in the partial results (i.e.
the inputs of the join). The role of the budget B=(k,m,c) in our synthesis algorithm is explained in
Section 5 of our paper.
Another way of using the tool on an input is to allow it to search for any budget, which lets the
tool perform the loop described in Figure 5. To do so, omit the optional arguments `-k`, `-m` and
`-c` when calling the tool, for example:
```
./Parsynt inputs/table1/pareto.minic
```
The reviewer may want to stop the tool from running too long after it has produced the first
solutions. The names of the files containing the solutions will be printed on the standard output.
During testing, the tool will probably discover more solutions than shown in the paper (e.g. a
solution with budget (1,2,2) for the sorting algorithm) but it may be that a linear join is
trivially a constant time join. We reported only the interesting solutions in the paper.

#### Benchmarks of Table 7a
The benchmarks in Table 7a have implementations that are splitting divide-and-conquer
implementations. A solution consists of the following components:
- A *lifted function*, which is the input function augmented with some additional computation. The
  body of the loop (or the fold) is a single struct corresponding to the update of the state
  variables of the loop. One may easily simplify it by factoring common sub-expressions.
- A *join function* which combines two partial results by applying the lifted function on sub-lists of
  an input list, in a divide-and-conquer manner. The body of the join is also written as a single
  struct. Note the expressions returned by Rosette are not syntactically the simplest, and despite a
  few simplifications performed by our tool, the resulting join may still look overly complicated.
- A *predicate* which constrains where the lists can be split, if one wishes to use the reference
  function in place of the lifted function in a divide-and-conquer algorithm. The predicate is
  written as an expression of elements of the list; the corresponding splitting divide splits the
  list such that the predicate holds at the point where the list is split.

The reviewer can run the tool on the *longest increasing sequence* (LIS) benchmark used as a running
example in our paper. To do so, run the following command from the root folder:
```./Parsynt inputs/table7a/lis.minic```
Note that the budget is irrelevant here: for a linear input function, the join has to be constant
time for the solution to be of acceptable complexity.
The lifted function contains four new auxiliary variables with suffix `aux`. There is one
more variable in Example 6.6. This is because the algorithm first lifts the `cl` variable. But the
auxiliary is unnecessary if one understands that this information can be recovered using the
information computed by g_1 in Example 6.6.
The splitting predicate should be equivalent to `a(-1) >= a(0)`, indicating that if the function is
not lifted then the list needs to be split such that the first element on the right of the split is
less than the last element before the split.
Finally, the output specifies the join function, a function of two structs containing the partial
results from a left and a right sub-list that has been split at an arbitrary point.


## (ii) Quality of the solutions

In order to run these experiments, the Intel TBB needs to be installed. The instructions
for building the exectuables are at the end of this file.

The synthesis of divide-and-conquer algorithms is motivated in our paper by different experiments
that show the practical performance benefits of the synthesized solutions. The reviewer can
easily compile the Figures 4, 7a and 7b from the existing data by running the scripts:
`./scripts/figure4.sh`
`./scripts/figure7b.sh`
`./scripts/figure7c.sh`
The outputs are PDF figures that are copied at the root folder with names matching the scripts
(files `figure(4|7a|7b).pdf`).
We also provide additional experimental data on the right column of page 11 of the paper. The
figure is a summary of Figure 12 in the Appendix. The reviewer can compile the 6 graphs appearing
in Figure 12 by running the script `./figure12.sh`. The figures are copied in the root folder,
with one file for each graph of Figure 12.

### Generating your own data

We also provide scripts that allow the reviewer to reproduce scaled-down version of our experiments.
Those scripts are the `generate*.sh` scripts at the root folder, with names matching the figure they
generate data for. At the top of each script are placed the variables that the reviewer can easily
modify. The parameters have been set so that the scripts can be run in a few minutes, in order to
check that the scripts are in functioning order. The reviewers should be especially interested in
changing the size of the experiments (EXPSIZE) and the number of times the experiment is repeated
(REPEATS) inside the shell scripts. In order to obtain reliable results, the reviewer should
run the experiments with a size large enough (suggestions provided in the scripts) and enough
repetitions (at least 10).

- `./scripts/generate4.sh` generates data for the experiments in Figure 4 and copies the resulting figure in
  `fig4_bis.pdf`.
- `./scripts/generate7b.sh` corresponds to Figure 7b. The output is `fig7b_bis.pdf`. For this experiment,
  the number of threads is set to 4, assuming the reviewer has at least 4 cores. The parameter
  MAX_THREADS can be changed depending on the number of cores available (16 in the paper).
- `./scripts/generate7c.sh` corresponds to Figure 7c, the output is `fig7c_bis.pdf`. The parameters should
  be modified similarly to the previous script.
- `./scripts/generate12.sh` corresponds to Figure 12 and the summary graphs on page 11 of the paper. This
  experiment will take more time than other. We suggest trying first with the parameters given
  before increasing the size of the inputs. The implementations are sequential implementations, but
  the script takes advantage of multiple processes to run experiments in parallel.

Note that for the benchmarks of Table 1, the running time may vary significantly across runs. For each
instance, the data is randomly generated (see `src/datagen.c`). The efficiency of the partitioning,
as mentioned in our paper, is highly dependent on the distribution of the input data.
--------------------
# Using Parsynt

## Building the tool

Parsynt is provided with all its source code in the `bin` and `lib` folders. The tool can be built
from the source by simply running `make` in the root folder. The software is mostly written in Ocaml
and uses the (dune)[https://dune.build] build system. To clean the built files and build again, run:
```
dune clean
make
```
The file `Parsynt` in the root folder links to the executable compiled in
`_build/default/bin/Parsynt.exe'.

The inputs are specified in a toy language with basic iteration constructs. The tool could be
interfaced with other programming languages in the future. In order to get an idea of how to write
your own inputs, you can have a look at the commented implementations of the two main examples used
in the paper: the *longest increasing sequence* implementation in `inputs/table7a/lis.minic` and the
Pareto Optimal Points implementation in `inputs/table1/pareto.minic`. Both the files contain
comments explaining the input language supported. In the current version, we limit the inputs to at
most two nested loops, and the base types are integer and booleans.
Additionally, `./Parsynt --help` provides information about the options that Parsynt can accept.


## Building the Experiments

We have implemented the divide-and-conquer algorithm synthesized from the benchmarks in
`experiments/src`. We use the (Intel's TBB library)[https://github.com/oneapi-src/oneTBB]
to implement the parallel benchmarks.
In order to build the experiments from source, change directory to experiments and run:
```
make clean
rm CMakeCache.txt # optional
cmake .
make
```
One executable is created for every benchmark in Table 1 and Table 7a, the executables
prefixed with 'Pd' correspond to benchmarks in Table 7a, and the executables prefixed
with 'Pt' are benchmarks from Table 1.


