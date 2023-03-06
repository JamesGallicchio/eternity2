#!/bin/bash
#SBATCH -A mth210009p
#SBATCH -N 1
#SBATCH -p RM
#SBATCH -t 24:00:00                  # set duration of the job
#SBATCH --ntasks=1                   # task = one (potentially multithread) computation
#SBATCH --cpus-per-task=128
#SBATCH -o run_test_solve_times.o%j # set output name of log file

#echo commands to stdout
set -x

BOARD_SUITE=~/eternity2/puzzles/board_suite
LOG_FILE=~/log/test_times_$SLURM_JOB_ID.csv

~/eternity2/lean/build/bin/eternity2 test-solve-times --boardsuite $BOARD_SUITE "${@}" > $LOG_FILE
