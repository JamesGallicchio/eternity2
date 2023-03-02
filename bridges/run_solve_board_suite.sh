#!/bin/bash

BOARD_SUITE=~/eternity2/puzzles/board_suite
LOG_FILE=~/log/solve_board_suite_$1.log

~/eternity2/lean/build/bin/eternity2 solve-board-suite --suite $BOARD_SUITE --logfile $LOG_FILE "${@:2}"
