#!/bin/sh

eval "./Parsy.native test/experiments/$1.c"
eval "dafny2 dafny_examples/Example_$1.dfy"

if [ -z "$2" ]
then
    echo "Finished."
else
    echo "cat dafny_examples/Example_$1.dfy"
    echo ""
    cat -n dafny_examples/Example_$1.dfy
fi
