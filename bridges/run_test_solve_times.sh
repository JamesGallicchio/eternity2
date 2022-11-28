#!/bin/bash

BOARD_SUITE=~/eternity2/board_suite
TIMEOUT=$1
OUTPUT=~/log/test_times_$TIMEOUT.csv

~/eternity2/lean/build/bin/eternity2 test-solve-times --boardsuite $BOARD_SUITE --timeout $TIMEOUT > $OUTPUT
