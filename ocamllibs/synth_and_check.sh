#!/bin/sh

if [ "$#" -ne 1 ]; then
    echo "Usage: ./synth_and_check.sh example_name [output_proof]"
    echo ""
    exit 0
fi

eval "./Parsy.native test/experiments/$1.c"
eval "dafny2 dafny_examples/Example_$1.dfy"

if [ -z "$2" ]
then
    echo "Finished."
else
    echo "----------------------------------------"
    echo "Proof in Dafny:"
    echo "----------------------------------------"
    cat -n dafny_examples/Example_$1.dfy
fi
