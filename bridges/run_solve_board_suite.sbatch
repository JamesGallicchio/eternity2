#!/bin/bash
#SBATCH -A mth210009p
#SBATCH -N 1
#SBATCH -p RM
#SBATCH -t 24:00:00                  # set duration of the job
#SBATCH --ntasks=1                   # task = one (potentially multithread) computation
#SBATCH --cpus-per-task=128
#SBATCH -o run_solve_board_suite.o%j # set output name of log file

#echo commands to stdout
set -x

LOG_FILE=~/log/solve_board_suite_$SLURM_JOB_ID.log

~/eternity2/lean/build/bin/eternity2 solve-board-suite --logfile $LOG_FILE "${@}"
