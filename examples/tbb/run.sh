#!/bin/sh


for EX_SIZE in 20 25 26 27 28 29 30 31 32
do
    for NUM_CORE in 0 1 2 4 6 8 16 32 64
    do
	eval "./tbb_test -n$NUM_CORE -e$EX_SIZE"
    done
done
