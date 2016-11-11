#!/bin/sh

EX_SIZE=20
while [  $EX_SIZE -lt 31 ]; do
    #Run the experiment with num_core 0 to get the sequential time
    eval "./tbb_test -n0 -e$EX_SIZE"
    #Run the experiment with 1 to 64 cores
    NUM_CORE=1
    while [  $NUM_CORE -lt 65 ]; do
	eval "./tbb_test -n$NUM_CORE -e$EX_SIZE"
	let NUM_CORE=NUM_CORE*2
    done
    let EX_SIZE=EX_SIZE+1
done
