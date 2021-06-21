#!/bin/sh
cd "$(dirname "$0")"
cd experiments
# python pop_sequential_experiment.py
python3 data/plot_pt_exp_seqs.py  --input data/exp_pt_seq/ptexpkla.csv --size 100000 --xlabel 'ratio k / size of input' >> /dev/null
cp data/exp_experiment_100000.pdf ../fig12a.pdf
python3 data/plot_pt_exp_seqs.py  --input data/exp_pt_seq/ptexpclo.csv --size 100000 --xlabel 'ratio of sorted elements' >> /dev/null
cp data/exp_experiment_100000.pdf ../fig12b.pdf
python3 data/plot_pt_exp_seqs.py  --input data/exp_pt_seq/ptexpins.csv --size 10000 --xlabel 'ratio of intersecting pairs' --plot33 >> /dev/null
cp data/exp_experiment_10000.pdf ../fig12c.pdf
python3 data/plot_pt_exp_seqs.py  --input data/exp_pt_seq/ptexphis.csv --size 100000 --xlabel 'ratio number of classes / size of input'      >> /dev/null
cp data/exp_experiment_100000.pdf ../fig12d.pdf
python3 data/plot_pt_exp_seqs.py  --input data/exp_pt_seq/ptexpmip.csv --size 100000 --xlabel 'minimal points / total points' >> /dev/null
cp data/exp_experiment_100000.pdf ../fig12e.pdf
python3 data/plot_pt_exp_seqs.py  --input data/exp_pt_seq/ptexpqoc.csv --size 100000 --xlabel 'ratio points in convex hull / total points' >> /dev/null
cp data/exp_experiment_100000.pdf ../fig12f.pdf
cd ..
echo "Outputs in fig12(a-f).pdf"

