#!/bin/sh
cd "$(dirname "$0")"
cd experiments
# python pop_sequential_experiment.py
python3 data/plot_pt_exp_seqs.py >> /dev/null
cp data/exp_experiment_100000.pdf ../figure4.pdf
cd ..
echo "Output in figure4.pdf"