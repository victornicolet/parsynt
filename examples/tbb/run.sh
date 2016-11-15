#!/bin/sh


for EX_SIZE in 31
do
    for NUM_CORE in -1 0 1 2 4 8 16 24 32 40 48 56 64
    do
	eval "./tbb_test -n$NUM_CORE -e$EX_SIZE"
	eval "./tbb_test -n$NUM_CORE -e$EX_SIZE"
    done
done
