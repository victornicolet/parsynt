#!/bin/sh
# Input size (pareto is quadratic or nlog(n) in input size)
EXPSIZE=2000 # for review, try 10000. For the paper: 100000
# Num processes for parallel experiments, not parallel execution of POP
NUM_PROCESSES=2
# How many times the experiment is repeated
REPEATS=2

# Start
TMP_CSV=data/tmp4.csv
cd "$(dirname "$0")"
cd experiments
rm -f $TMP_CSV
python3 gen_data_fig4.py --output $TMP_CSV --sizes $EXPSIZE --numprocs $NUM_PROCESSES --repeats $REPEATS
mv data/exp_ptexppop_$EXPSIZE.pdf ../fig4_bis.pdf
rm -f $TMP_CSV
cd ..
echo "Output in fig4_bis.pdf"