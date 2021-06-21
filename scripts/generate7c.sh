#!/bin/sh
# Input size (lis is linear in input size)
EXPERIMENT_SIZE=1240000 # in the paper, EXPSIZE=1705032704
# Maximum number of threads for parallel implementations.
MAX_THREADS=4 # change according to hardware
# How many times the experiment is repeated.
REPEATS=3

TMPFILE=data/tmp7c.csv
cd "$(dirname "$0")"
cd experiments
rm -f $TMPFILE
python3 gen_data_fig7c.py --expsize $EXPERIMENT_SIZE --max-cores $MAX_THREADS --repeats $REPEATS --output $TMPFILE
FIG=$(python3 data/plot_figure7c.py $TMPFILE 0)
mv $FIG ../fig7c_bis.pdf
rm -f $TMPFILE
cd ..
echo "Output in fig7c_bis.pdf"
