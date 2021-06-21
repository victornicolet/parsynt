#!/bin/sh

# Input size (pareto is quadratic or nlog(n) in input size)
EXPSIZE=2048 # for review, try 10000. For the paper: 100000
# Num processes for parallel experiments, not parallel execution of POP
NUM_PROCESSES=2
# How many times the experiment is repeated
REPEATS=2

# Start
cd "$(dirname "$0")"
cd experiments
# K Largest
touch data/tmp/ptexpkla.csv
python3 gen_data_fig4.py --output data/tmp/ptexpkla.csv --sizes $EXPSIZE --binary ./PtExpKla --numprocs $NUM_PROCESSES --repeats $REPEATS
# Closest pairs
touch data/tmp/ptexpclo.csv
python3 gen_data_fig4.py --output data/tmp/ptexpclo.csv --sizes $EXPSIZE --binary ./PtExpClo --numprocs $NUM_PROCESSES --repeats $REPEATS
# Intersecting Segments
touch data/tmp/ptexpins.csv
python3 gen_data_fig4.py --output data/tmp/ptexpins.csv --sizes $EXPSIZE --binary ./PtExpIns --numprocs $NUM_PROCESSES --repeats $REPEATS
# Histogram
touch data/tmp/ptexphis.csv
python3 gen_data_fig4.py --output data/tmp/ptexphis.csv --sizes $EXPSIZE --binary ./PtExpHis --numprocs $NUM_PROCESSES --repeats $REPEATS
# Minimum Points
touch data/tmp/ptexpmip.csv
python3 gen_data_fig4.py --output data/tmp/ptexpmip.csv --sizes $EXPSIZE --binary ./PtExpMip --numprocs $NUM_PROCESSES --repeats $REPEATS
# Quadrant Orthogonal Convex Hull
touch data/tmp/ptexpqoc.csv
python3 gen_data_fig4.py --output data/tmp/ptexpqoc.csv --sizes $EXPSIZE --binary ./PtExpQoc --numprocs $NUM_PROCESSES --repeats $REPEATS


# Plot
python3 data/plot_pt_exp_seqs.py  --input data/tmp/ptexpkla.csv --size $EXPSIZE --xlabel 'ratio k / size of input' >> /dev/null
cp data/exp_experiment_$EXPSIZE.pdf ../fig12a_bis.pdf
python3 data/plot_pt_exp_seqs.py  --input data/tmp/ptexpclo.csv --size $EXPSIZE --xlabel 'ratio of sorted elements' >> /dev/null
cp data/exp_experiment_$EXPSIZE.pdf ../fig12b_bis.pdf
python3 data/plot_pt_exp_seqs.py  --input data/tmp/ptexpins.csv --size $EXPSIZE --xlabel 'ratio of intersecting pairs' --plot33 >> /dev/null
cp data/exp_experiment_$EXPSIZE.pdf ../fig12c_bis.pdf
python3 data/plot_pt_exp_seqs.py  --input data/tmp/ptexphis.csv --size $EXPSIZE --xlabel 'ratio number of classes / size of input' >> /dev/null
cp data/exp_experiment_$EXPSIZE.pdf ../fig12d_bis.pdf
python3 data/plot_pt_exp_seqs.py  --input data/tmp/ptexpmip.csv --size $EXPSIZE --xlabel 'minimal points / total points' >> /dev/null
cp data/exp_experiment_$EXPSIZE.pdf ../fig12e_bis.pdf
python3 data/plot_pt_exp_seqs.py  --input data/tmp/ptexpqoc.csv --size $EXPSIZE --xlabel 'ratio points in convex hull / total points' >> /dev/null
cp data/exp_experiment_$EXPSIZE.pdf ../fig12f_bis.pdf
# Cleanup plots
rm -f data/exp_*.pdf
cd ..
echo "Outputs in figures fig12(a-f)_bis.pdf"
