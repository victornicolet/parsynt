#!/bin/sh
cd "$(dirname "$0")"
cd experiments
OUTPUT7C=$(python3 data/plot_figure7c.py data/lis_data.csv)
mv $OUTPUT7C ../figure7c.pdf
cd ..
echo "Output in figure7c.pdf"
