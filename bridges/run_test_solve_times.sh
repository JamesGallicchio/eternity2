#!/bin/bash

BOARD_SUITE=~/eternity2/board_suite

OUTPUT=~/log/test_times_$1.csv

~/eternity2/lean/build/bin/eternity2 test-solve-times --boardsuite $BOARD_SUITE "${@:2}" > $OUTPUT
