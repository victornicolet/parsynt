#!/bin/sh
cd "$(dirname "$0")"
cd experiments

OUTPUT7B=$(python3 data/plot_figure7b.py)
mv $OUTPUT7B ../figure7b.pdf
cd ..
echo "output in figure7b.pdf"
