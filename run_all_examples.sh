#!/bin/bash

declare -a ALL_EXAMPLES=("sum.c" "min.c" "max.c" "hamming.c" "length.c" "2nd_min.c" "mps.c" "mts.c" "mss.c" "mts_p.c" "mps_p.c" "poly.c" "atoi.c" "is_sorted.c" "dropwhile.c" "balanced_parenthesis.c" "0star1star.c" "count_1s.c" "line_sight.c" "0after1.c")

for EXAMPLE in "${ALL_EXAMPLES[@]}"
do
    ./Parsy.native examples/c/experiments/$EXAMPLE
done
