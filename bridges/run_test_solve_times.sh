#!/bin/bash

BOARD_SUITE=~/eternity2/board_suite
TIMEOUT=$1
if [ -z "$2" ]
then
    OUTPUT=~/log/test_times_$TIMEOUT.csv
else
    OUTPUT=$2/test_times_$TIMEOUT.csv
fi

~/eternity2/lean/build/bin/eternity2 test-solve-times --boardsuite $BOARD_SUITE --timeout $TIMEOUT > $OUTPUT
