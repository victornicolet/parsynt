#!/bin/sh
# Input size (the functions are linear in input size)
EXPSIZE=1240000 # in the paper, EXPSIZE=1705032704
# Maximum number of threads for parallel implementations.
MAX_THREADS=4 # change according to hardware
# How many times the experiment is repeated.
REPEATS=3

# Start
cd "$(dirname "$0")"
cd experiments
rm -f data/tmp.csv
python3 gen_data_fig7b.py --expsize $EXPSIZE --max-cores $MAX_THREADS --repeats $REPEATS --output data/tmp.csv
FIG=$(python3 data/plot_figure7b.py --input data/tmp.csv --insize $EXPSIZE)
mv $FIG ../fig7b_bis.pdf
rm data/tmp.csv
cd ..
echo "Output in fig7b_bis.pdf"