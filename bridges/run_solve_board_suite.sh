#!/bin/bash

LOG_FILE=~/log/solve_board_suite_$1.log

~/eternity2/lean/build/bin/eternity2 solve-board-suite --logfile $LOG_FILE "${@:2}"
