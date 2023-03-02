#!/bin/bash

BOARD_SUITE=~/eternity2/puzzle/board_suite

OUTPUT=~/log/solve_board_suite_$1.csv

~/eternity2/lean/build/bin/eternity2 solve-board-suite --suite $BOARD_SUITE "${@:2}" > $OUTPUT
