#!/bin/bash

#Check for Racket installation
echo "Checking Racket installation ..."
RACKET_VERSION=$(racket -v | sed -n 's/^.*Racket v\([0-9]*.[0-9]*\).*$/\1/p')
if [ -z $RACKET_VERSION ]
then
    echo "FAIL : Racket not installed ! Please install Racket."
    exit 0
else
    if [[ $(bc <<< "$RACKET_VERSION > 6.0") ]]
    then
        echo "OK : Racket" $RACKET_VERSION "is installed."
    else
        echo "FAIL : Racket" $RACKET_VERSION "is installed, we need at least 6.0."
        echo "Please install a more recent version of Racket."
        exit 0
    fi
fi

MAYBE_INSTALLED=$(raco pkg show consynth)
